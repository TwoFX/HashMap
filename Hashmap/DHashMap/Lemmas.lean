/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.WF

set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace MyLean.DHashMap

namespace Raw₀

variable (m : Raw₀ α β) (h : m.1.WF)

/-! # Lemmas about model implementations -/

theorem findEntry?ₘ_insertₘ (a k : α) (b : β a) :
    (m.insertₘ a b).findEntry?ₘ k = bif a == k then some ⟨a, b⟩ else m.findEntry?ₘ k := by
  rw [findEntry?ₘ_eq_findEntry? _ (wfImp_insertₘ _ h.out _ _), findEntry?ₘ_eq_findEntry? _ h.out,
    List.findEntry?_of_perm (wfImp_insertₘ _ h.out _ _).distinct (toListModel_insertₘ _ h.out _ _),
    List.findEntry?_insertEntry]

theorem containsₘ_eq_isSome_findEntry?ₘ {a : α} : m.containsₘ a = (m.findEntry?ₘ a).isSome := by
  rw [findEntry?ₘ_eq_findEntry? _ h.out, containsₘ_eq_containsKey h.out, List.containsKey_eq_isSome_findEntry?]

/-! # Lemmas about actual implementations -/

theorem findEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).1.findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_findEntry?ₘ, insert_eq_insertₘ, findEntry?_eq_findEntry?ₘ, findEntry?ₘ_insertₘ _ h]

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome := by
  rw [findEntry?_eq_findEntry?ₘ, contains_eq_containsₘ, containsₘ_eq_isSome_findEntry?ₘ _ h]

end Raw₀

namespace Raw

variable (m : Raw α β) (h : m.WF)

theorem findEntry?_insert {a k : α} {b : β a} :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [insert_eq h, findEntry?_eq h, findEntry?_eq h.insert₀, Raw₀.findEntry?_insert ⟨m, _⟩ h]

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome := by
  rw [contains_eq h, findEntry?_eq h, Raw₀.contains_eq_isSome_findEntry? ⟨m, _⟩ h]

end Raw

section

variable (m : DHashMap α β)

theorem findEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k :=
  Raw₀.findEntry?_insert ⟨m.1, _⟩ m.2 a k b

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome :=
  Raw₀.contains_eq_isSome_findEntry? ⟨m.1, _⟩ m.2

end

end MyLean.DHashMap
