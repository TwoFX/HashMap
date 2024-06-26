/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Lemmas

/-!
# Dependent hash map showcase: structure with cached field

In this file, we construct an (artificial) example of the "extreme case" of a hash map: a dependent hash map
in which the key does not have a `LawfulBEq` instance. The example we use is this: a structure `Range` which has
a field `size'` which is only computed on demand (see the `getSize` function). In this specific example, the
computation is very cheap, so this design does not make much sense in this case, but one can imagine other cases
where we want this kind of behavior. Since this on-demand field represents "transient" information, it is not
included in the `BEq` and `Hashable` instances. The `BEq` instance is therefore not lawful (but and equivalence
relation, so it is fine from the perspective of the hash map). We then define a type family `Partition` on `Range`
which is "good" in the sense that it actually only depends on the non-transient fields of `Partition`, as witnessed
by the function `Partition.cast : {t t' : Range} → t == t' → Partition t → Partition t'`. Then we imagine we have
a `DHashMap Range (Partition ·)`, and try to work with it. We observe that getting information that matches the
key out of the hash map is quite painful in `getPartitionAsDepList` below. There are various ways one could try
to make this easier:

1. Provide a function `getWithCast? (m : DHashMap α β) (a : α) (cast : ∀ a', a' == a → β a' → β a) : Option (β a)`
   that lets you provide the casting function, or
2. Introduce a typeclass

   class HasPathLifting (α : Type u) [BEq α] (β : α → Type v) where
     lift {a b : α} : a == b → β a → β b

   that characterizes families that allow for convenient hash map access. Note that both the non-dependent case and
   the case `LawfulBEq α` are special cases of this.
-/

open Std

structure Range where
  start : Nat
  stop : Nat
  size' : Option Nat

def Range.getSize (t : Range) : Range × Nat :=
  if h : t.size'.isSome then
    (t, t.size'.get h)
  else
    let size := t.stop - t.start
    ({ t with size' := some size }, size)

protected def Range.beq : Range → Range → Bool
  | ⟨start₁, stop₁, _⟩, ⟨start₂, stop₂, _⟩ => start₁ = start₂ && stop₁ = stop₂

instance : BEq Range where
  beq := Range.beq

@[simp]
theorem Range.beq_iff {t₁ t₂ : Range} : t₁ == t₂ ↔ t₁.start = t₂.start ∧ t₁.stop = t₂.stop := by
  rcases t₁ with ⟨start₁, stop₁, -⟩
  rcases t₂ with ⟨start₂, stop₂, -⟩
  change start₁ = start₂ && stop₁ = stop₂ ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq]

protected def Range.hash : Range → UInt64
  | ⟨start, stop, _⟩ => mixHash (hash start) (hash stop)

instance : Hashable Range where
  hash := Range.hash

instance : LawfulHashable Range where
  hash_eq a b h := match a, b with | ⟨_, _, _⟩, ⟨_, _, _⟩ => by rcases Range.beq_iff.1 h with ⟨rfl, rfl⟩; rfl

section EquivBEq

/-!
In this section we introduce a model structure without the irrelevant data to pull back the
`EquivBEq` instance.
-/

structure RangeModel where
  start : Nat
  stop : Nat
deriving DecidableEq

def Range.toModel : Range → RangeModel
  | ⟨start, stop, _⟩ => ⟨start, stop⟩

theorem Range.beq_toModel : (t₁ t₂ : Range) → (t₁.toModel == t₂.toModel) = (t₁ == t₂)
  | ⟨_, _, _⟩, ⟨_, _, _⟩ => Bool.eq_iff_iff.2 <| by simp [toModel]

instance : EquivBEq Range :=
  .of_embedding Range.toModel (fun {a b} => by rw [Range.beq_toModel])

end EquivBEq

structure Partition (t : Range) where
  points : List Nat
  in_range : ∀ s ∈ points, t.start ≤ s ∧ s ≤ t.stop

def Partition.asDepList {t : Range} : (p : Partition t) → List ({ s : Nat // t.start ≤ s ∧ s ≤ t.stop })
  | ⟨[], _⟩ => []
  | ⟨s :: ss, h⟩ => ⟨s, h _ (List.mem_cons_self _ _)⟩ :: asDepList ⟨ss, fun s' h' => h _ (List.mem_cons_of_mem _ h')⟩

abbrev M := ReaderM (DHashMap Range Partition)

/-- This is the good case: here we can get the information we want without having to cast. -/
def hasLargePartition (t : Range) : M Bool := do
  match (← read).findEntry? t with
  | none => return false
  | some ⟨_, partition⟩ => return (partition.points.length ≥ 20)

def Partition.cast : {t t' : Range} → t == t' → Partition t → Partition t'
  | ⟨_, _, _⟩, ⟨_, _, _⟩, h, ⟨l, hl⟩ => ⟨l, by obtain ⟨rfl, rfl⟩ := Range.beq_iff.1 h; assumption⟩

/-- This is the painful case, where we want information about the key we are searching for. But `findWithCast?` makes
    this quite feasible. -/
def getPartitionAsDepList (t : Range) : M <| Option <| List <| {s : Nat // t.start ≤ s ∧ s ≤ t.stop } := do
  return (← read).findWithCast? t Partition.cast |>.map Partition.asDepList

/-!
On a completely unrelated note, some observations about the IR of alternative implementations of `getSize`.
-/
-- -- This one gives exactly the same IR as the implementation above
-- def Range.getSize' : Range → Range × Nat
--   | t@⟨start, stop, size'⟩ =>
--     match size' with
--     | none =>
--       let size := stop - start
--       (⟨start, stop, some size⟩, size)
--     | some size =>
--       (t, size)

-- -- Sadly, this one doesn't
-- def Range.getSize'' : Range → Range × Nat
--   | ⟨start, stop, size'⟩ =>
--     match size' with
--     | none =>
--       let size := stop - start
--       (⟨start, stop, some size⟩, size)
--     | some size =>
--       (⟨start, stop, some size⟩, size)
