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

@[simp]
theorem findEntry?_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).findEntry? a = none := by
  rw [findEntry?_eq_findEntry?ₘ]
  simp [findEntry?ₘ_eq_findEntry? _ Raw.WF.empty₀.out]

@[simp]
theorem find?_empty {β : Type v} {a : α} {c : Nat} : (empty c : Raw₀ α (fun _ => β)).find? a = none := by
  rw [find?_eq_find?ₘ]
  simp [find?ₘ_eq_findValue? _ Raw.WF.empty₀.out]

theorem findEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).1.findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_findEntry?ₘ, insert_eq_insertₘ, findEntry?_eq_findEntry?ₘ]
  rw [findEntry?ₘ_eq_findEntry? _ (wfImp_insertₘ _ h.out _ _), findEntry?ₘ_eq_findEntry? _ h.out,
    List.findEntry?_of_perm (wfImp_insertₘ _ h.out _ _).distinct (toListModel_insertₘ _ h.out _ _),
    List.findEntry?_insertEntry]

theorem find?_insert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (a k : α) (b : β) :
    (m.insert a b).1.find? k = bif a == k then some b else m.find? k := by
  rw [find?_eq_find?ₘ, insert_eq_insertₘ, find?_eq_find?ₘ]
  rw [find?ₘ_eq_findValue? _ (wfImp_insertₘ _ h.out _ _), find?ₘ_eq_findValue? _ h.out,
    List.findValue?_of_perm (wfImp_insertₘ _ h.out _ _).distinct (toListModel_insertₘ _ h.out _ _),
    List.findValue?_insertEntry]

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome := by
  rw [findEntry?_eq_findEntry?ₘ, contains_eq_containsₘ]
  rw [findEntry?ₘ_eq_findEntry? _ h.out, containsₘ_eq_containsKey h.out, List.containsKey_eq_isSome_findEntry?]

end Raw₀

namespace Raw

variable (m : Raw α β) (h : m.WF)

@[simp]
theorem findEntry?_empty {a : α} {c : Nat} : (empty c : Raw α β).findEntry? a = none := by
  rw [empty_eq, findEntry?_eq WF.empty₀, Raw₀.findEntry?_empty]

@[simp]
theorem findEntry?_emptyc {a : α} : (∅ : Raw α β).findEntry? a = none :=
  findEntry?_empty

@[simp]
theorem find?_empty {β : Type v} {a : α} {c : Nat} : (empty c : Raw α (fun _ => β)).find? a = none := by
  rw [empty_eq, find?_eq WF.empty₀, Raw₀.find?_empty]

@[simp]
theorem find?_emptyc {β : Type v} {a : α} : (∅ : Raw α (fun _ => β)).find? a = none :=
  find?_empty

theorem findEntry?_insert {a k : α} {b : β a} :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [insert_eq h, findEntry?_eq h, findEntry?_eq h.insert₀, Raw₀.findEntry?_insert ⟨m, _⟩ h]

theorem find?_insert {β : Type v} (m : Raw α (fun _ => β)) (h : m.WF) (a k : α) (b : β) :
    (m.insert a b).find? k = bif a == k then some b else m.find? k := by
  rw [insert_eq h, find?_eq h, find?_eq h.insert₀, Raw₀.find?_insert ⟨m, _⟩ h]

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome := by
  rw [contains_eq h, findEntry?_eq h, Raw₀.contains_eq_isSome_findEntry? ⟨m, _⟩ h]

end Raw

section

variable (m : DHashMap α β)

@[simp]
theorem findEntry?_empty {a : α} {c : Nat} : (empty c : DHashMap α β).findEntry? a = none :=
  Raw₀.findEntry?_empty

@[simp]
theorem findEntry?_emptyc {a : α} : (∅ : DHashMap α β).findEntry? a = none :=
  Raw₀.findEntry?_empty

@[simp]
theorem find?_empty {β : Type v} {a : α} {c : Nat} : (empty c : DHashMap α (fun _ => β)).find? a = none :=
  Raw₀.find?_empty

@[simp]
theorem find?_emptyc {β : Type v} {a : α} : (∅ : DHashMap α (fun _ => β)).find? a = none :=
  Raw₀.find?_empty

theorem findEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k :=
  Raw₀.findEntry?_insert ⟨m.1, _⟩ m.2 a k b

theorem find?_insert {β : Type v} (m : DHashMap α (fun _ => β)) (a k : α) (b : β) :
    (m.insert a b).find? k = bif a == k then some b else m.find? k :=
  Raw₀.find?_insert ⟨m.1, _⟩ m.2 _ _ _

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome :=
  Raw₀.contains_eq_isSome_findEntry? ⟨m.1, _⟩ m.2

end

end MyLean.DHashMap
