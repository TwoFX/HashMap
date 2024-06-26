/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Internal.WF

/-!
This file defines operations on `DHashMap` which cannot be defined in `Basic.lean` due to universe issues.
This file will have more imports than `Basic.lean` once everything is properly untangled.
-/

open MyLean.DHashMap.Internal

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

namespace MyLean.DHashMap

namespace Raw

open Internal.Raw

theorem WF.filterMap [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → Option (δ a)} :
    (m.filterMap f).WF := by
  simpa only [filterMap_eq h] using .wf (Raw₀.filterMap f ⟨m, h.size_buckets_pos⟩).2 (Internal.Raw.WFImp.filterMap h.out)

theorem WF.map [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → δ a} :
    (m.map f).WF := by
  simpa only [map_eq h] using .wf (Raw₀.map f ⟨m, h.size_buckets_pos⟩).2 (Internal.Raw.WFImp.map h.out)

end Raw

@[inline] def filterMap [BEq α] [Hashable α] (f : (a : α) → β a → Option (δ a)) (m : DHashMap α β) : DHashMap α δ :=
  ⟨Raw₀.filterMap f ⟨m.1, m.2.size_buckets_pos⟩, .wf (Raw₀.filterMap f ⟨m.1, m.2.size_buckets_pos⟩).2 (Internal.Raw.WFImp.filterMap m.2.out)⟩

@[inline] def map [BEq α] [Hashable α] (f : (a : α) → β a → δ a) (m : DHashMap α β) : DHashMap α δ :=
  ⟨Raw₀.map f ⟨m.1, m.2.size_buckets_pos⟩, .wf (Raw₀.map f ⟨m.1, m.2.size_buckets_pos⟩).2 (Internal.Raw.WFImp.map m.2.out)⟩

end MyLean.DHashMap
