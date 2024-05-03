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

namespace Model

theorem findEntry?_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.WF) (a k : α) (b : β a) :
    findEntry? (insert m a b) k = bif a == k then some ⟨a, b⟩ else findEntry? m k := by
  rw [findEntry?_eq_findEntry? _ (ActuallyWF_insert _ h.out _ _), findEntry?_eq_findEntry? _ h.out,
    List.findEntry?_of_perm (ActuallyWF_insert _ h.out _ _).distinct (toListModel_insert _ h.out _ _),
    List.findEntry?_insertEntry]

end Model

namespace Raw₀

theorem findEntry?_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.WF) (a k : α) (b : β a) :
    (m.insert a b).1.findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_model, insert_eq_model, findEntry?_eq_model, Model.findEntry?_insert _ h]

end Raw₀

theorem findEntry?_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (m : DHashMap α β) (a k : α) (b : β a) :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k :=
  Raw₀.findEntry?_insert ⟨m.1, _⟩ m.2 a k b

end MyLean.DHashMap
