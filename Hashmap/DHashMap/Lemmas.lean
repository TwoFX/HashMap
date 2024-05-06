/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.WF

set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v}

namespace MyLean.DHashMap

namespace Raw₀

theorem findEntry?ₘ_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.WF) (a k : α) (b : β a) :
    findEntry?ₘ (m.insertₘ a b) k = bif a == k then some ⟨a, b⟩ else findEntry?ₘ m k := by
  rw [findEntry?ₘ_eq_findEntry? _ (wfImp_insertₘ _ h.out _ _), findEntry?ₘ_eq_findEntry? _ h.out,
    List.findEntry?_of_perm (wfImp_insertₘ _ h.out _ _).distinct (toListModel_insertₘ _ h.out _ _),
    List.findEntry?_insertEntry]

theorem findEntry?_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.WF) (a k : α) (b : β a) :
    (m.insert a b).1.findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_findEntry?ₘ, insert_eq_insertₘ, findEntry?_eq_findEntry?ₘ, findEntry?ₘ_insert _ h]

end Raw₀

theorem findEntry?_insert [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (m : DHashMap α β) (a k : α) (b : β a) :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k :=
  Raw₀.findEntry?_insert ⟨m.1, _⟩ m.2 a k b

end MyLean.DHashMap
