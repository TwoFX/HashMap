/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.AssocList.Basic
import Hashmap.LawfulHashable
import Std.Data.Array.Lemmas

set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v}

namespace MyLean

namespace DHashMap

structure Raw (α : Type u) (β : α → Type v) where
  size : Nat
  buckets : Array (AssocList α β)

namespace Raw

private def numBucketsForCapacity (capacity : Nat) : Nat :=
  -- a "load factor" of 0.75 is the usual standard for hash maps
  capacity * 4 / 3

def empty (capacity := 8) : Raw α β where
  size := 0
  buckets := mkArray (numBucketsForCapacity capacity).nextPowerOfTwo AssocList.nil

private def mkIdx {sz : Nat} (hash : UInt64) (h : 0 < sz) : { u : USize // u.toNat < sz } :=
  -- TODO: restore this to hash.toUSize &&& (sz.toUSize - 1). This is not so easy because we probably (?) don't want
  -- to check for m.buckets.size.isPowerOfTwo in Raw.insert, right?
  ⟨hash.toUSize % sz, Nat.mod_lt _ h⟩

@[inline] def reinsertAux [Hashable α]
    (data : { d : Array (AssocList α β) // 0 < d.size }) (a : α) (b : β a) : { d : Array (AssocList α β) // 0 < d.size } :=
  let ⟨data, hd⟩ := data
  let ⟨i, h⟩ := mkIdx (hash a) hd
  ⟨data.uset i (data[i].cons a b) h, by simpa⟩

/-- Copies all the entries from `buckets` into a new hash map with a larger capacity. -/
def expand [Hashable α] (size : Nat) (data : { d : Array (AssocList α β) // 0 < d.size }) : { m : Raw α β // 0 < m.buckets.size } :=
  let ⟨data, hd⟩ := data
  let nbuckets := data.size * 2
  let ⟨newBuckets, hn⟩ := go 0 data ⟨mkArray nbuckets AssocList.nil, by rw [Array.size_mkArray]; exact Nat.mul_pos hd Nat.two_pos⟩
  ⟨{ size, buckets := newBuckets }, hn⟩
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
      let target := es.foldl reinsertAux target
      go (i+1) source target
    else target
  termination_by source.size - i

@[inline] def insertWellFormed [BEq α] [Hashable α] (m : { m : Raw α β // 0 < m.buckets.size }) (a : α) (b : β a) :
    { m : Raw α β // 0 < m.buckets.size } × Bool :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx (hash a) hm
  let bkt := buckets[i]
  if bkt.contains a then
    (⟨⟨size, buckets.uset i (bkt.replace a b) h⟩, by simpa⟩, true)
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    if numBucketsForCapacity size' ≤ buckets.size then
      (⟨{ size := size', buckets := buckets'}, by simpa [buckets']⟩, false)
    else
      (expand size' ⟨buckets', by simpa [buckets']⟩, false)

@[inline] def insert' [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β × Bool :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, replaced⟩ := insertWellFormed ⟨m, h⟩ a b
    ⟨r, replaced⟩
  else (m, false) -- will never happen for well-formed inputs

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  (insert' m a b).1

@[inline] def findEntry?WellFormed [BEq α] [Hashable α] (m : { m : Raw α β // 0 < m.buckets.size }) (a : α) :
    Option (Σ a, β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx (hash a) h
  buckets[i].findEntry? a

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option (Σ a, β a) :=
  if h : 0 < m.buckets.size then
    findEntry?WellFormed ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

section WF

def toList (m : Raw α β) : List (Σ a, β a) :=
  m.buckets.data.bind AssocList.toList

structure IsHashSelf [BEq α] [Hashable α] (m : Raw α β) : Prop where
  hashes_to (i : Nat) (h : i < m.buckets.size) : m.buckets[i].toList.HashesTo i m.buckets.size

structure WF [BEq α] [Hashable α] (m : Raw α β) extends IsHashSelf m : Prop where
  buckets_size : m.buckets.size.isPowerOfTwo
  size_eq : m.size = m.toList.length
  distinct : m.toList.WF

end WF

end Raw

inductive WF [BEq α] [Hashable α] : Raw α β → Prop where
  | wf : ∀ m, m.WF → WF m
  | insert : ∀ m h a b, WF (Raw.insertWellFormed ⟨m, h⟩ a b).1.1

theorem WF.size_buckets_pos [BEq α] [Hashable α] (m : Raw α β) : WF m → 0 < m.buckets.size
  | wf m h => Nat.pos_of_isPowerOfTwo h.buckets_size
  | insert m h a b => (Raw.insertWellFormed ⟨m, h⟩ a b).1.2

end DHashMap

def DHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] := { m : DHashMap.Raw α β // DHashMap.WF m }

namespace DHashMap

@[inline] def insert' [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  let m' := Raw.insertWellFormed ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨⟨m'.1.1, .insert _ _ _ _⟩, m'.2⟩

@[inline] def insert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  (m.insert' a b).1

@[inline] def findEntry? [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (Σ a, β a) :=
  Raw.findEntry?WellFormed ⟨m.1, m.2.size_buckets_pos⟩ a

end MyLean.DHashMap
