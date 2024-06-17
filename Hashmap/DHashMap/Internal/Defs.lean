/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.DHashMap.Raw
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

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β × Bool :=
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

@[inline] def insertIfNewThenGetM [BEq α] [Hashable α] [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
    (q : Raw₀ α β) (a : α) (f : Unit → m (β a)) : m (Raw₀ α β × β a) :=
  let ⟨⟨size, buckets⟩, hm⟩ := q
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  match bkt.getCast? a with
  | none => do
      let v ← f ()
      let size'    := size + 1
      let buckets' := buckets.uset i (AssocList.cons a v bkt) h
      return (expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩, v)
  | some v => pure (⟨⟨size, buckets⟩, hm⟩, v)

@[inline] def insertIfNewThenGet [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α) (f : Unit → β a) : Raw₀ α β × β a :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  match bkt.getCast? a with
  | none =>
      let v := f ()
      let size'    := size + 1
      let buckets' := buckets.uset i (AssocList.cons a v bkt) h
      (expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩, v)
  | some v => (⟨⟨size, buckets⟩, hm⟩, v)

@[inline] def getEntry? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (Σ a, β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].getEntry? a

@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].getCast? a

@[inline, specialize] def getWithCast? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (cast : ∀ {b}, b == a → β b → β a) : Option (β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].getWithCast? a cast

@[inline] def contains [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].contains a

@[inline] def getEntry [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (hma : m.contains a) : Σ a, β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getEntry a hma

@[inline, specialize] def getWithCast [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (cast : ∀ {b}, b == a → β b → β a) (hma : m.contains a) : β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getWithCast a cast hma

@[inline] def get [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (hma : m.contains a) : β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getCast a hma

def remove [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hb⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hb (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    let buckets' := buckets.uset i .nil h
    ⟨⟨size - 1, buckets'.uset i (bkt.remove a) (by simpa [buckets'])⟩, by simpa [buckets']⟩
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

@[inline] def Const.get? [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].get? a

@[inline] def Const.get [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (hma : m.contains a) : β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].get a hma

end

end Raw₀

end MyLean.DHashMap