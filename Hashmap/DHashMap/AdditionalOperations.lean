/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.WF

/-!
This file defines operations on `DHashMap` which cannot be defined in `Basic.lean` due to universe issues.
This file will have more imports than `Basic.lean` once everything is properly untangled.
-/

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

namespace MyLean.DHashMap

namespace Raw₀

-- @[inline] def computeIfAbsentM [BEq α] [Hashable α] [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
--     (q : Raw₀ α β) (a : α) (f : Unit → m (β a)) : m ({ r : Raw₀ α β // q.1.WF → r.1.WF } × β a) :=
--   let ⟨⟨size, buckets⟩, hm⟩ := q
--   let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
--   let bkt := buckets[i]
--   match bkt.findCast? a with
--   | none => do
--       let v ← f ()
--       let size'    := size + 1
--       let buckets' := buckets.uset i (AssocList.cons a v bkt) h
--       return (⟨expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets', -List.length_pos]⟩, _⟩, v)
--   | some v => pure (⟨⟨⟨size, buckets⟩, hm⟩, id⟩, v)

end Raw₀

-- @[inline] def computeIfAbsentM [BEq α] [LawfulBEq α] [Hashable α] {β : α → Type u} {m : Type u → Type v}
--     [Monad m] (q : DHashMap α β) (a : α) (f : Unit → m (β a)) : m (DHashMap α β × β a) := do
--   let m' ← Raw₀.computeIfAbsentM ⟨q.1, q.2.size_buckets_pos⟩ a f
--   return ⟨⟨m'.1.1, _⟩, m'.2⟩

def filterMap [BEq α] [Hashable α] (f : (a : α) → β a → Option (δ a)) (m : DHashMap α β) : DHashMap α δ :=
  ⟨Raw₀.filterMap f ⟨m.1, m.2.size_buckets_pos⟩, .wf (Raw₀.filterMap f ⟨m.1, m.2.size_buckets_pos⟩).2 m.2.out.filterMap⟩

def map [BEq α] [Hashable α] (f : (a : α) → β a → δ a) (m : DHashMap α β) : DHashMap α δ :=
  ⟨Raw₀.map f ⟨m.1, m.2.size_buckets_pos⟩, .wf (Raw₀.map f ⟨m.1, m.2.size_buckets_pos⟩).2 m.2.out.map⟩

end MyLean.DHashMap
