/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.AssocList.Basic
import Hashmap.LawfulHashable
import Batteries.Data.Array.Lemmas
import Hashmap.DHashMap.Index

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v}

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
  ⟨data.uset i (data[i].cons a b) h, by simpa [-List.length_pos]⟩

/-- Copies all the entries from `buckets` into a new hash map with a larger capacity. -/
def expand [Hashable α] (data : { d : Array (AssocList α β) // 0 < d.size }) : { d : Array (AssocList α β) // 0 < d.size } :=
  let ⟨data, hd⟩ := data
  let nbuckets := data.size * 2
  let ⟨newBuckets, hn⟩ := go 0 data ⟨mkArray nbuckets AssocList.nil, by simpa [nbuckets] using Nat.mul_pos hd Nat.two_pos⟩
  ⟨newBuckets, hn⟩
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
    let ⟨buckets', h'⟩ := expand ⟨buckets, by simpa [-List.length_pos]⟩
    ⟨⟨size, buckets'⟩, h'⟩

@[inline] def insert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β × Bool :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    (⟨⟨size, buckets.uset i (bkt.replace a b) h⟩, by simpa [-List.length_pos]⟩, true)
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    (expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets', -List.length_pos]⟩, false)

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (Σ a, β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].findEntry? a

@[inline] def find? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].findCast? a

@[inline] def contains [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].contains a

def erase [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hb⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hb (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    ⟨⟨size - 1, buckets.uset i (bkt.erase a) h⟩, by simpa [-List.length_pos]⟩
  else
    ⟨⟨size, buckets⟩, hb⟩

@[specialize] def filterMap₁ {γ : α → Type w} (f : (a : α) → β a → Option (γ a))
    (m : Raw₀ α β) : Raw₀ α γ :=
  let ⟨⟨_, buckets⟩, hb⟩ := m
  let newBuckets := buckets.map (AssocList.filterMap f)
  ⟨⟨computeSize newBuckets, newBuckets⟩, by simpa [-List.length_pos, newBuckets] using hb⟩

section

variable {β : Type v}

@[inline] def findConst? [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].find? a

end

end Raw₀

namespace Raw

@[inline] def empty (capacity := 8) : Raw α β :=
  (Raw₀.empty capacity).1

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

@[inline] def insert' [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β × Bool :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, replaced⟩ := Raw₀.insert ⟨m, h⟩ a b
    ⟨r, replaced⟩
  else (m, false) -- will never happen for well-formed inputs

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  (insert' m a b).1

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option (Σ a, β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.findEntry? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def find? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β) (a : α) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.find? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  if h : 0 < m.buckets.size then
    Raw₀.contains ⟨m, h⟩ a
  else false -- will never happen for well-formed inputs

@[inline] def erase [BEq α] [Hashable α] (m : Raw α β) (a : α) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.erase ⟨m, h⟩ a
  else m -- will never happen for well-formed inputs

section

variable {β : Type v}

@[inline] def findConst? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) : Option β :=
  if h : 0 < m.buckets.size then
    Raw₀.findConst? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

end

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
  | wf {m} : m.WFImp → WF m
  | empty₀ {c} : WF (Raw₀.empty c).1
  | insert₀ {m h a b} : WF m → WF (Raw₀.insert ⟨m, h⟩ a b).1.1
  | erase₀ {m h a} : WF m → WF (Raw₀.erase ⟨m, h⟩ a).1

theorem WF.size_buckets_pos [BEq α] [Hashable α] (m : Raw α β) : WF m → 0 < m.buckets.size
  | wf h => h.buckets_size
  | empty₀ => (Raw₀.empty _).2
  | insert₀ _ => (Raw₀.insert ⟨_, _⟩ _ _).1.2
  | erase₀ _ => (Raw₀.erase ⟨_, _⟩ _).2

theorem WF.insert' [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insert' a b).1.WF := by
  simpa [Raw.insert', h.size_buckets_pos] using .insert₀ h

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insert a b).WF :=
  WF.insert' h

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
@[inline] def insert' [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  let m' := Raw₀.insert ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨⟨m'.1.1, .insert₀ m.2⟩, m'.2⟩

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
-/
@[inline] def insert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  (m.insert' a b).1

/--
Retrieves the mapping associated with the given key, if it exists.
-/
@[inline] def findEntry? [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (Σ a, β a) :=
  Raw₀.findEntry? ⟨m.1, m.2.size_buckets_pos⟩ a

/--
Retrieves the value associated with the given key, if it exists. This function requires a `LawfulBEq` instance
to be able to cast the value to the correct type. If no such instance is available, you can use `findEntry?`
or switch to a non-dependent `HashMap`.
-/
@[inline] def find? [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (β a) :=
  Raw₀.find? ⟨m.1, m.2.size_buckets_pos⟩ a

/-- Returns true if the hash map contains a mapping with a key equal to the given key. -/
@[inline] def contains [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Bool :=
  Raw₀.contains ⟨m.1, m.2.size_buckets_pos⟩ a

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

end MyLean.DHashMap
