/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.AssocList.Map
import Hashmap.LawfulHashable
import Std.Data.Array.Lemmas

namespace MyLean

namespace HashMap.Imp

def Buckets (α : Type u) [BEq α] (β : α → Type v) :=
  { t : Array (AssocListMap α β) // t.size.isPowerOfTwo }

namespace Buckets

def update [BEq α] (b : Buckets α β) (i : Fin b.1.size) (l : AssocListMap α β) : Buckets α β :=
  ⟨b.1.set i l, by simpa using b.2⟩

@[simp]
theorem update_size [BEq α] {b : Buckets α β} (i : Fin b.1.size) {l : AssocListMap α β} :
    (b.update i l).1.size = b.1.size := by simp [update]

theorem update_get [BEq α] {b : Buckets α β} {i : Fin b.1.size} {l : AssocListMap α β}
    {j : Fin (b.update i l).1.size}:
    (b.update i l).1[j] = if (i : Nat) = j then l else b.1[j] := by
  simp [update]
  rw [Array.get_set]

private def mkIdx {sz : Nat} (hash : UInt64) (h : sz.isPowerOfTwo) : { u : USize // u.toNat < sz } :=
  -- TODO: avoid `if` in the reference implementation
  let u := hash.toUSize &&& (sz.toUSize - 1)
  if h' : u.toNat < sz then
    ⟨u, h'⟩
  else
    ⟨0, by simp [USize.toNat, OfNat.ofNat, USize.ofNat, Fin.ofNat']; apply Nat.pos_of_isPowerOfTwo h⟩

def mkIdx' {sz : Nat} (hash : UInt64) (h : sz.isPowerOfTwo) : Fin sz :=
  let i := mkIdx hash h; ⟨i.1.toNat, i.2⟩

structure BucketWFAt [BEq α] [Hashable α] (l : AssocListMap α β)
    {size : Nat} (h : size.isPowerOfTwo) (i : Nat) : Prop where
  hash_valid [LawfulHashable α] : ∀ a, l.contains a → (mkIdx (hash a) h).1.toNat = i

theorem BucketWFAt_nil [BEq α] [Hashable α] {size : Nat} (h : size.isPowerOfTwo) {i : Nat} :
    BucketWFAt (AssocListMap.nil : AssocListMap α β) h i where
  hash_valid a h := by simp at h

theorem BucketWFAt_erase [BEq α] [EquivBEq α] [Hashable α] {l : AssocListMap α β} {k : α} {size : Nat}
    (h : size.isPowerOfTwo) {i : Nat} :
    BucketWFAt l h i → BucketWFAt (l.erase k) h i :=
  fun ⟨h⟩ => ⟨fun a h' => h a <| l.contains_of_contains_erase h'⟩

theorem BucketWFAt_insert [BEq α] [EquivBEq α] [Hashable α] {l : AssocListMap α β} {k : α} {v : β k} {size : Nat}
    (h' : size.isPowerOfTwo) {i : Nat}
    (h : (mkIdx (hash k) h').1.toNat = i) : BucketWFAt l h' i → BucketWFAt (l.insert k v) h' i := by
  refine fun ⟨h₁⟩ => ⟨fun a h'' => ?_⟩
  rw [l.contains_insert, Bool.or_eq_true] at h''
  rcases h'' with (h''|h'')
  · rwa [← hash_eq_of_beq h'']
  · exact h₁ _ h''

structure WF [BEq α] [Hashable α] [LawfulHashable α] (b : Buckets α β) : Prop where
  bucket_wf : ∀ (i : Fin b.1.size), BucketWFAt b.1[i] b.2 i

theorem WF_update [BEq α] [Hashable α] [LawfulHashable α] {b : Buckets α β} {i : Fin b.1.size}
    {l : AssocListMap α β} : b.WF → BucketWFAt l b.2 i → (b.update i l).WF := by
  refine fun ⟨h₁⟩ h₂ => ⟨fun j => ?_⟩
  rw [update_get]
  by_cases h' : i.1 = j
  · simpa [h'] using h₂
  · simp [h']
    apply h₁ (Fin.cast (by simp) j)

-- def bucketFor [BEq α] [Hashable α] (b : Buckets α β) (k : α) : AssocListMap α β :=
--   b.1[mkIdx' (hash k) b.2]

def contains [BEq α] [Hashable α] (b : Buckets α β) (k : α) : Bool :=
  b.1[mkIdx' (hash k) b.2].contains k

def cons [BEq α] [Hashable α] (b : Buckets α β) (k : α) (v : β k) (h : b.contains k = false) : Buckets α β :=
  let idx := mkIdx' (hash k) b.2;
  b.update idx (b.1[idx].cons k v h)

@[simp]
theorem contains_cons [BEq α] [Hashable α] (b : Buckets α β) {k a : α} {v : β k} {h : b.contains k = false} :
    (b.cons k v h).contains a = (k == a || b.contains a) := sorry

structure Consable [BEq α] [Hashable α] (b : Buckets α β) (l : AssocListMap α β) : Prop where
  contains : ∀ a, l.contains a → b.contains a = false

theorem Consable.cons_out [BEq α] [EquivBEq α] [Hashable α] {b : Buckets α β} {l : AssocListMap α β} {k : α}
    {v : β k} {h : l.contains k = false} : Consable b (l.cons k v h) → b.contains k = false
  | ⟨h⟩ => h _ (by simp)

theorem consable_nil [BEq α] [Hashable α] {b : Buckets α β} : Consable b AssocListMap.nil where
  contains := by simp

theorem consable_cons [BEq α] [EquivBEq α] [Hashable α] {b : Buckets α β}
    {l : AssocListMap α β} {k : α} {v : β k} {h : l.contains k = false}
      (hb : Consable b (l.cons k v h)) : Consable (b.cons k v hb.cons_out) l where
  contains a ha := by
    simp [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · -- Contradiction using h and ha
      sorry
    · apply hb.contains
      simpa using Or.inr ha

-- def addAll (b : Buckets α β) (l : AssocListMap α β) (h : ∀ a, l.contains a →

end Buckets

end HashMap.Imp

end MyLean
