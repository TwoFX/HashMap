/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.AssocList.Basic
import Hashmap.List.Defs
import Hashmap.BEq
import Hashmap.LawfulHashable
import Hashmap.DHashMap.Internal.Index
import Hashmap.Sigma

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace MyLean

namespace DHashMap

-- TODO: Move this to a better place
structure IsHashSelf [BEq α] [Hashable α] (m : Array (AssocList α β)) : Prop where
  hashes_to (i : Nat) (h : i < m.size) : m[i].toList.HashesTo i m.size

private def numBucketsForCapacity (capacity : Nat) : Nat :=
  -- a "load factor" of 0.75 is the usual standard for hash maps
  capacity * 4 / 3

def toListModel (buckets : Array (AssocList α β)) : List (Σ a, β a) :=
  buckets.data.bind AssocList.toList

def computeSize (buckets : Array (AssocList α β)) : Nat :=
  buckets.foldl (fun d b => d + b.length) 0

structure Raw (α : Type u) (β : α → Type v) where
  size : Nat
  buckets : Array (AssocList α β)

abbrev Raw₀ (α : Type u) (β : α → Type v) :=
  { m : Raw α β // 0 < m.buckets.size }

namespace Raw₀

@[inline] def empty (capacity := 8) : Raw₀ α β :=
  ⟨⟨0, mkArray (numBucketsForCapacity capacity).nextPowerOfTwo AssocList.nil⟩,
    by simpa using Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo _)⟩

-- Take `hash` as a function instead of `Hashable α` as per https://github.com/leanprover/lean4/issues/4191
@[inline] def reinsertAux (hash : α → UInt64)
    (data : { d : Array (AssocList α β) // 0 < d.size }) (a : α) (b : β a) : { d : Array (AssocList α β) // 0 < d.size } :=
  let ⟨data, hd⟩ := data
  let ⟨i, h⟩ := mkIdx data.size hd (hash a)
  ⟨data.uset i (data[i].cons a b) h, by simpa⟩

/-- Copies all the entries from `buckets` into a new hash map with a larger capacity. -/
def expand [Hashable α] (data : { d : Array (AssocList α β) // 0 < d.size }) : { d : Array (AssocList α β) // 0 < d.size } :=
  let ⟨data, hd⟩ := data
  let nbuckets := data.size * 2
  go 0 data ⟨mkArray nbuckets AssocList.nil, by simpa [nbuckets] using Nat.mul_pos hd Nat.two_pos⟩
where
  /-- Inner loop of `expand`. Copies elements `source[i:]` into `target`,
  destroying `source` in the process. -/
  go (i : Nat) (source : Array (AssocList α β)) (target : { d : Array (AssocList α β) // 0 < d.size }) :
      { d : Array (AssocList α β) // 0 < d.size } :=
    if h : i < source.size then
      let idx : Fin source.size := ⟨i, h⟩
      let es := source.get idx
      -- We remove `es` from `source` to make sure we can reuse its memory cells
      -- when performing es.foldl
      let source := source.set idx .nil
      let target := es.foldl (reinsertAux hash) target
      go (i+1) source target
    else target
  termination_by source.size - i

@[inline] def expandIfNecessary [BEq α] [Hashable α] (m : Raw₀ α β) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  if numBucketsForCapacity size ≤ buckets.size then
    ⟨⟨size, buckets⟩, hm⟩
  else
    let ⟨buckets', h'⟩ := expand ⟨buckets, by simpa⟩
    ⟨⟨size, buckets'⟩, h'⟩

@[inline] def insert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    let buckets' := buckets.uset i .nil h
    ⟨⟨size, buckets'.uset i (bkt.replace a b) (by simpa [buckets'])⟩, by simpa [buckets']⟩
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩

@[inline] def insertB [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β × Bool :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    let buckets' := buckets.uset i .nil h
    (⟨⟨size, buckets'.uset i (bkt.replace a b) (by simpa [buckets'])⟩, by simpa [buckets']⟩, true)
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    (expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩, false)

@[inline] def computeIfAbsentM [BEq α] [Hashable α] [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
    (q : Raw₀ α β) (a : α) (f : Unit → m (β a)) : m (Raw₀ α β × β a) :=
  let ⟨⟨size, buckets⟩, hm⟩ := q
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  match bkt.findCast? a with
  | none => do
      let v ← f ()
      let size'    := size + 1
      let buckets' := buckets.uset i (AssocList.cons a v bkt) h
      return (expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩, v)
  | some v => pure (⟨⟨size, buckets⟩, hm⟩, v)

@[inline] def computeIfAbsent [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α) (f : Unit → β a) : Raw₀ α β × β a :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  match bkt.findCast? a with
  | none =>
      let v := f ()
      let size'    := size + 1
      let buckets' := buckets.uset i (AssocList.cons a v bkt) h
      (expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩, v)
  | some v => (⟨⟨size, buckets⟩, hm⟩, v)

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (Σ a, β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].findEntry? a

@[inline] def find? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].findCast? a

@[inline, specialize] def findWithCast? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (cast : ∀ {b}, b == a → β b → β a) : Option (β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].findWithCast? a cast

@[inline] def contains [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].contains a

@[inline] def findEntry [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (hma : m.contains a) : Σ a, β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].findEntry a hma

@[inline, specialize] def findWithCast [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (cast : ∀ {b}, b == a → β b → β a) (hma : m.contains a) : β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].findWithCast a cast hma

@[inline] def find [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (hma : m.contains a) : β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].findCast a hma

def erase [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hb⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hb (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    let buckets' := buckets.uset i .nil h
    ⟨⟨size - 1, buckets'.uset i (bkt.erase a) (by simpa [buckets'])⟩, by simpa [buckets']⟩
  else
    ⟨⟨size, buckets⟩, hb⟩

-- Computing the size after the fact was determined to be faster than computing it inline,
-- see Benchmark/FilterMap.lean
@[specialize] def filterMap {γ : α → Type w} (f : (a : α) → β a → Option (γ a))
    (m : Raw₀ α β) : Raw₀ α γ :=
  let ⟨⟨_, buckets⟩, hb⟩ := m
  let newBuckets := buckets.map (AssocList.filterMap f)
  ⟨⟨computeSize newBuckets, newBuckets⟩, by simpa [newBuckets] using hb⟩

@[specialize] def map {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw₀ α β) : Raw₀ α γ :=
  let ⟨⟨size, buckets⟩, hb⟩ := m
  let newBuckets := buckets.map (AssocList.map f)
  ⟨⟨size, newBuckets⟩, by simpa [newBuckets] using hb⟩

section

variable {β : Type v}

@[inline] def findConst? [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].find? a

@[inline] def findConst [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (hma : m.contains a) : β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].find a hma

end

end Raw₀

namespace Raw

@[inline] def empty (capacity := 8) : Raw α β :=
  (Raw₀.empty capacity).1

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insert ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

@[inline] def insertB [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β × Bool :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, replaced⟩ := Raw₀.insertB ⟨m, h⟩ a b
    ⟨r, replaced⟩
  else (m, false) -- will never happen for well-formed inputs

@[inline] def computeIfAbsentM [BEq α] [Hashable α] [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
    (q : Raw α β) (a : α) (f : Unit → m (β a)) : m (Raw α β × β a) :=
  if h : 0 < q.buckets.size then do
    let ⟨⟨r, _⟩, s⟩ ← Raw₀.computeIfAbsentM ⟨q, h⟩ a f
    return (r, s)
  else return (q, ← f ()) -- will never happen for well-formed inputs

@[inline] def computeIfAbsent [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (f : Unit → β a) : Raw α β × β a :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, s⟩ := Raw₀.computeIfAbsent ⟨m, h⟩ a f
    (r, s)
  else (m, f ()) -- will never happen for well-formed inputs

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option (Σ a, β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.findEntry? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def find? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β) (a : α) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.find? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def findWithCast? [BEq α] [Hashable α] (m : Raw α β) (a : α) (cast : ∀ {b}, b == a → β b → β a) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.findWithCast? ⟨m, h⟩ a cast
  else none -- will never happen for well-formed inputs

@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  if h : 0 < m.buckets.size then
    Raw₀.contains ⟨m, h⟩ a
  else false -- will never happen for well-formed inputs

@[inline] def erase [BEq α] [Hashable α] (m : Raw α β) (a : α) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.erase ⟨m, h⟩ a
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

@[inline] def findConst? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) : Option β :=
  if h : 0 < m.buckets.size then
    Raw₀.findConst? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

end

/-- Folds the given function over the mappings in the hash map in some order. -/
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.foldlM (fun acc l => l.foldlM f acc) init

/-- Folds the given function over the mappings in the hash map in some order. -/
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (b : Raw α β) : δ :=
  Id.run (b.foldlM f init)

def beq [BEq α] [Hashable α] [LawfulBEq α] [∀ k, BEq (β k)] (m₁ m₂ : Raw α β) : Bool :=
  m₁.size = m₂.size && (m₁.foldl fun acc k v => acc && match m₂.find? k with
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
  m.size = 0

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
  | insertB₀ {m h a b} : WF m → WF (Raw₀.insertB ⟨m, h⟩ a b).1.1
  | erase₀ {m h a} : WF m → WF (Raw₀.erase ⟨m, h⟩ a).1
  | computeIfAbsent₀ [LawfulBEq α] {m h a f} : WF m → WF (Raw₀.computeIfAbsent ⟨m, h⟩ a f).1

theorem WF.size_buckets_pos [BEq α] [Hashable α] (m : Raw α β) : WF m → 0 < m.buckets.size
  | wf h₁ _ => h₁
  | empty₀ => (Raw₀.empty _).2
  | insert₀ _ => (Raw₀.insert ⟨_, _⟩ _ _).2
  | insertB₀ _ => (Raw₀.insertB ⟨_, _⟩ _ _).1.2
  | erase₀ _ => (Raw₀.erase ⟨_, _⟩ _).2
  | computeIfAbsent₀ _ => (Raw₀.computeIfAbsent ⟨_, _⟩ _ _).1.2

@[simp]
theorem WF.empty [BEq α] [Hashable α] {c : Nat} : (Raw.empty c : Raw α β).WF :=
  .empty₀

@[simp]
theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α β).WF :=
  .empty

theorem WF.insertB [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insertB a b).1.WF := by
  simpa [Raw.insertB, h.size_buckets_pos] using .insertB₀ h

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insert a b).WF := by
  simpa [Raw.insert, h.size_buckets_pos] using .insert₀ h

theorem WF.erase [BEq α] [Hashable α] {m : Raw α β} {a : α} (h : m.WF) : (m.erase a).WF := by
  simpa [Raw.erase, h.size_buckets_pos] using .erase₀ h

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
@[inline] def insertB [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  let m' := Raw₀.insertB ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨⟨m'.1.1, .insertB₀ m.2⟩, m'.2⟩

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
-/
@[inline] def insert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  ⟨Raw₀.insert ⟨m.1, m.2.size_buckets_pos⟩ a b, .insert₀ m.2⟩

/--
If the map contains a mapping for the given key, return the value. Otherwise, compute the value using the
given function, insert it into the map, and return the value.
-/
@[inline] def computeIfAbsent [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) (f : Unit → β a) : DHashMap α β × β a :=
  let m' := Raw₀.computeIfAbsent ⟨m.1, m.2.size_buckets_pos⟩ a f
  ⟨⟨m'.1.1, .computeIfAbsent₀ m.2⟩, m'.2⟩

/--
Retrieves the mapping associated with the given key, if it exists.
-/
@[inline] def findEntry? [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (Σ a, β a) :=
  Raw₀.findEntry? ⟨m.1, m.2.size_buckets_pos⟩ a

/--
Retrieves the value associated with the given key, if it exists. This function requires a `LawfulBEq` instance
to be able to cast the value to the correct type. If no such instance is available, you can use `findEntry?`,
`findWithCast?`,
or switch to a non-dependent `HashMap`.
-/
@[inline] def find? [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (β a) :=
  Raw₀.find? ⟨m.1, m.2.size_buckets_pos⟩ a

/--
Retrieves the value associated with the given key, if it exists, and casts the value to the correct dependent type using
the provided cast function.
-/
@[inline] def findWithCast? [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (cast : ∀ {b}, b == a → β b → β a) : Option (β a) :=
  Raw₀.findWithCast? ⟨m.1, m.2.size_buckets_pos⟩ a cast

/-- Returns true if the hash map contains a mapping with a key equal to the given key. -/
@[inline] def contains [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Bool :=
  Raw₀.contains ⟨m.1, m.2.size_buckets_pos⟩ a

-- instance [BEq α] [Hashable α] : GetElem (DHashMap α β) α (Σ a, β a) fun m a => m.contains a := sorry
-- instance [BEq α] [LawfulBEq α] [Hashable α] : DGetElem (DHashMap α β) α β fun m a => m.contains a := sorry

/--
Removes the mapping with the given key if it exists.
-/
@[inline] def erase [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : DHashMap α β :=
  ⟨Raw₀.erase ⟨m.1, m.2.size_buckets_pos⟩ a, .erase₀ m.2⟩

section

variable {β : Type v}

/--
Retrieves the value associated with the given key, if it exists. -/
@[inline] def findConst? [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) : Option β :=
  Raw₀.findConst? ⟨m.1, m.2.size_buckets_pos⟩ a

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
