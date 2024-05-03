/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.WF

set_option autoImplicit false

universe u v

variable {α : Type v} {β : α → Type v}

namespace MyLean.DHashMap

namespace Raw₀

theorem findEntry?_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.WF) (a k : α) (b : β a) :
    (m.insert a b).1.findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_findEntry? _ h.out, findEntry?_eq_findEntry?]
  · rw [insert_eq_model, List.findEntry?_of_perm _ (toListModel_insert _ _ _ _), List.findEntry?_insertEntry]
    · exact (ActuallyWF.insert _ h.out _ _).distinct
    · exact h.out
  · rw [insert_eq_model]
    exact ActuallyWF.insert _ h.out _ _

end Raw₀

theorem findEntry?_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (m : DHashMap α β) (a k : α) (b : β a) :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k :=
  Raw₀.findEntry?_insert ⟨m.1, _⟩ m.2 a k b

end MyLean.DHashMap
