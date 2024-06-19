/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.DHashMap.Internal.Defs

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace MyLean

namespace DHashMap

namespace Raw

@[inline] def empty (capacity := 8) : Raw α β :=
  (Raw₀.empty capacity).1

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insert ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β × Bool :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, replaced⟩ := Raw₀.containsThenInsert ⟨m, h⟩ a b
    ⟨r, replaced⟩
  else (m, false) -- will never happen for well-formed inputs

@[inline] def insertIfNewThenGetM [BEq α] [Hashable α] [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
    (q : Raw α β) (a : α) (f : Unit → m (β a)) : m (Raw α β × β a) :=
  if h : 0 < q.buckets.size then do
    let ⟨⟨r, _⟩, s⟩ ← Raw₀.insertIfNewThenGetM ⟨q, h⟩ a f
    return (r, s)
  else return (q, ← f ()) -- will never happen for well-formed inputs

@[inline] def insertIfNewThenGet [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (f : Unit → β a) : Raw α β × β a :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, s⟩ := Raw₀.insertIfNewThenGet ⟨m, h⟩ a f
    (r, s)
  else (m, f ()) -- will never happen for well-formed inputs

@[inline] def getEntry? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option (Σ a, β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.getEntry? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β) (a : α) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def getWithCast? [BEq α] [Hashable α] (m : Raw α β) (a : α) (cast : ∀ {b}, b == a → β b → β a) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.getWithCast? ⟨m, h⟩ a cast
  else none -- will never happen for well-formed inputs

@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  if h : 0 < m.buckets.size then
    Raw₀.contains ⟨m, h⟩ a
  else false -- will never happen for well-formed inputs

@[inline] def remove [BEq α] [Hashable α] (m : Raw α β) (a : α) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.remove ⟨m, h⟩ a
  else m -- will never happen for well-formed inputs

@[inline] def filterMap {γ : α → Type w} (f : (a : α) → β a → Option (γ a)) (m : Raw α β) : Raw α γ :=
  if h : 0 < m.buckets.size then
    Raw₀.filterMap f ⟨m, h⟩
  else ∅ -- will never happen for well-formed inputs

@[inline] def map {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw α β) : Raw α γ :=
  if h : 0 < m.buckets.size then
    Raw₀.map f ⟨m, h⟩
  else ∅ -- will never happen for well-formed inputs

section

variable {β : Type v}

@[inline] def Const.get? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) : Option β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

end

/-- Folds the given function over the mappings in the hash map in some order. -/
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.foldlM (fun acc l => l.foldlM f acc) init

/-- Folds the given function over the mappings in the hash map in some order. -/
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (b : Raw α β) : δ :=
  Id.run (b.foldlM f init)

def beq [BEq α] [Hashable α] [LawfulBEq α] [∀ k, BEq (β k)] (m₁ m₂ : Raw α β) : Bool :=
  m₁.size = m₂.size && (m₁.foldl fun acc k v => acc && match m₂.get? k with
  | none => false
  | some v' => v == v') true

instance [BEq α] [Hashable α] [LawfulBEq α] [∀ k, BEq (β k)] : BEq (Raw α β) where
  beq := beq

def toList (m : Raw α β) : List (Σ a, β a) :=
  m.foldl (fun acc k v => ⟨k, v⟩ :: acc) []

def toArray (m : Raw α β) : Array (Σ a, β a) :=
  m.foldl (fun acc k v => acc.push ⟨k, v⟩) #[]

def toListConst {β : Type v} (m : Raw α (fun _ => β)) : List (α × β) :=
  m.foldl (fun acc k v => ⟨k, v⟩ :: acc) []

def toArrayConst {β : Type v} (m : Raw α (fun _ => β)) : Array (α × β) :=
  m.foldl (fun acc k v => acc.push ⟨k, v⟩) #[]

def values {β : Type v} (m : Raw α (fun _ => β)) : List β :=
  m.foldl (fun acc _ v => v :: acc) []

def isEmpty (m : Raw α β) : Bool :=
  m.size == 0

section WF

/--
This is the actual well-formedness predicate for hash maps. Users should never need to interact with this and should use
`WF` instead.
-/
structure WFImp [BEq α] [Hashable α] (m : Raw α β) : Prop where
  buckets_hash_self : IsHashSelf m.buckets
  buckets_size : 0 < m.buckets.size
  size_eq : m.size = (toListModel m.buckets).length
  distinct : (toListModel m.buckets).DistinctKeys

/--
Well-formedness predicate for hash maps. Users of `DHashMap` will not need to interact with this. Users of `HashMap.Raw`
will need to provide proofs of `WF` to lemmas and should use the lemmas `WF.empty`, `WF.insert'` and `WF.insert` to show
that map operations preserve well-formedness.
-/
inductive WF [BEq α] [Hashable α] : Raw α β → Prop where
  | wf {m} : 0 < m.buckets.size → (∀ [EquivBEq α] [LawfulHashable α], m.WFImp) → WF m
  | empty₀ {c} : WF (Raw₀.empty c).1
  | insert₀ {m h a b} : WF m → WF (Raw₀.insert ⟨m, h⟩ a b).1
  | containsThenInsert₀ {m h a b} : WF m → WF (Raw₀.containsThenInsert ⟨m, h⟩ a b).1.1
  | remove₀ {m h a} : WF m → WF (Raw₀.remove ⟨m, h⟩ a).1
  | insertIfNewThenGet₀ [LawfulBEq α] {m h a f} : WF m → WF (Raw₀.insertIfNewThenGet ⟨m, h⟩ a f).1

theorem WF.size_buckets_pos [BEq α] [Hashable α] (m : Raw α β) : WF m → 0 < m.buckets.size
  | wf h₁ _ => h₁
  | empty₀ => (Raw₀.empty _).2
  | insert₀ _ => (Raw₀.insert ⟨_, _⟩ _ _).2
  | containsThenInsert₀ _ => (Raw₀.containsThenInsert ⟨_, _⟩ _ _).1.2
  | remove₀ _ => (Raw₀.remove ⟨_, _⟩ _).2
  | insertIfNewThenGet₀ _ => (Raw₀.insertIfNewThenGet ⟨_, _⟩ _ _).1.2

@[simp]
theorem WF.empty [BEq α] [Hashable α] {c : Nat} : (Raw.empty c : Raw α β).WF :=
  .empty₀

@[simp]
theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α β).WF :=
  .empty

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.containsThenInsert a b).1.WF := by
  simpa [Raw.containsThenInsert, h.size_buckets_pos] using .containsThenInsert₀ h

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insert a b).WF := by
  simpa [Raw.insert, h.size_buckets_pos] using .insert₀ h

theorem WF.remove [BEq α] [Hashable α] {m : Raw α β} {a : α} (h : m.WF) : (m.remove a).WF := by
  simpa [Raw.remove, h.size_buckets_pos] using .remove₀ h

end WF

end Raw

end DHashMap

def DHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] := { m : DHashMap.Raw α β // m.WF }

namespace DHashMap

/-- Constructs an empty hash map with a number of buckets appropriate for the given size. -/
@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : DHashMap α β :=
  ⟨Raw.empty capacity, .empty₀⟩

instance [BEq α] [Hashable α] : EmptyCollection (DHashMap α β) where
  emptyCollection := empty

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
Returns `true` if there was a previous mapping that was replaced.
-/
@[inline] def containsThenInsert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  let m' := Raw₀.containsThenInsert ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨⟨m'.1.1, .containsThenInsert₀ m.2⟩, m'.2⟩

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
-/
@[inline] def insert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  ⟨Raw₀.insert ⟨m.1, m.2.size_buckets_pos⟩ a b, .insert₀ m.2⟩

/--
If the map contains a mapping for the given key, return the value. Otherwise, compute the value using the
given function, insert it into the map, and return the value.
-/
@[inline] def insertIfNewThenGet [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) (f : Unit → β a) : DHashMap α β × β a :=
  let m' := Raw₀.insertIfNewThenGet ⟨m.1, m.2.size_buckets_pos⟩ a f
  ⟨⟨m'.1.1, .insertIfNewThenGet₀ m.2⟩, m'.2⟩

/--
Retrieves the mapping associated with the given key, if it exists.
-/
@[inline] def getEntry? [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (Σ a, β a) :=
  Raw₀.getEntry? ⟨m.1, m.2.size_buckets_pos⟩ a

/--
Retrieves the value associated with the given key, if it exists. This function requires a `LawfulBEq` instance
to be able to cast the value to the correct type. If no such instance is available, you can use `getEntry?`,
`getWithCast?`,
or switch to a non-dependent `HashMap`.
-/
@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (β a) :=
  Raw₀.get? ⟨m.1, m.2.size_buckets_pos⟩ a

/--
Retrieves the value associated with the given key, if it exists, and casts the value to the correct dependent type using
the provided cast function.
-/
@[inline] def getWithCast? [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (cast : ∀ {b}, b == a → β b → β a) : Option (β a) :=
  Raw₀.getWithCast? ⟨m.1, m.2.size_buckets_pos⟩ a cast

/-- Returns true if the hash map contains a mapping with a key equal to the given key. -/
@[inline] def contains [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Bool :=
  Raw₀.contains ⟨m.1, m.2.size_buckets_pos⟩ a

/--
Removes the mapping with the given key if it exists.
-/
@[inline] def remove [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : DHashMap α β :=
  ⟨Raw₀.remove ⟨m.1, m.2.size_buckets_pos⟩ a, .remove₀ m.2⟩

section

variable {β : Type v}

/--
Retrieves the value associated with the given key, if it exists. -/
@[inline] def Const.get? [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) : Option β :=
  Raw₀.Const.get? ⟨m.1, m.2.size_buckets_pos⟩ a

end

def size [BEq α] [Hashable α] (m : DHashMap α β) : Nat :=
  m.1.size

instance [BEq α] [Hashable α] [LawfulBEq α] [∀ k, BEq (β k)] : BEq (DHashMap α β) where
  beq m₁ m₂ := m₁.1 == m₂.1

def toList [BEq α] [Hashable α] (m : DHashMap α β) : List (Σ a, β a) :=
  m.1.toList

def toArray [BEq α] [Hashable α] (m : DHashMap α β) : Array (Σ a, β a) :=
  m.1.toArray

def values {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) : List β :=
  m.1.values

def isEmpty [BEq α] [Hashable α] (m : DHashMap α β) : Bool :=
  m.1.isEmpty

end MyLean.DHashMap
