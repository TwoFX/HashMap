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
  simp [findEntry?_eq_findEntry? Raw.WF.empty₀.out]

@[simp]
theorem findConst?_empty {β : Type v} {a : α} {c : Nat} : (empty c : Raw₀ α (fun _ => β)).findConst? a = none := by
  simp [findConst?_eq_findValue? Raw.WF.empty₀.out]

theorem findEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).1.findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_findEntry? h.out.insert, findEntry?_eq_findEntry? h.out,
    List.findEntry?_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.findEntry?_insertEntry]

theorem findConst?_insert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (a k : α) (b : β) :
    (m.insert a b).1.findConst? k = bif a == k then some b else m.findConst? k := by
  rw [findConst?_eq_findValue? h.out.insert, findConst?_eq_findValue? h.out,
    List.findValue?_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.findValue?_insertEntry]

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome := by
  rw [findEntry?_eq_findEntry? h.out, contains_eq_containsKey h.out, List.containsKey_eq_isSome_findEntry?]

theorem findEntry?_eq_some (a : α) (p : Σ a, β a) (h : m.findEntry? a = some p) : p.1 == a :=
  AssocList.findEntry?_eq_some h

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
theorem findConst?_empty {β : Type v} {a : α} {c : Nat} : (empty c : Raw α (fun _ => β)).findConst? a = none := by
  rw [empty_eq, findConst?_eq WF.empty₀, Raw₀.findConst?_empty]

@[simp]
theorem findConst?_emptyc {β : Type v} {a : α} : (∅ : Raw α (fun _ => β)).findConst? a = none :=
  findConst?_empty

theorem findEntry?_insert {a k : α} {b : β a} :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [insert_eq h, findEntry?_eq h, findEntry?_eq h.insert₀, Raw₀.findEntry?_insert ⟨m, _⟩ h]

theorem findConst?_insert {β : Type v} (m : Raw α (fun _ => β)) (h : m.WF) (a k : α) (b : β) :
    (m.insert a b).findConst? k = bif a == k then some b else m.findConst? k := by
  rw [insert_eq h, findConst?_eq h, findConst?_eq h.insert₀, Raw₀.findConst?_insert ⟨m, _⟩ h]

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
theorem findConst?_empty {β : Type v} {a : α} {c : Nat} : (empty c : DHashMap α (fun _ => β)).findConst? a = none :=
  Raw₀.findConst?_empty

@[simp]
theorem findConst?_emptyc {β : Type v} {a : α} : (∅ : DHashMap α (fun _ => β)).findConst? a = none :=
  Raw₀.findConst?_empty

theorem findEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k :=
  Raw₀.findEntry?_insert ⟨m.1, _⟩ m.2 a k b

theorem findConst?_insert {β : Type v} (m : DHashMap α (fun _ => β)) (a k : α) (b : β) :
    (m.insert a b).findConst? k = bif a == k then some b else m.findConst? k :=
  Raw₀.findConst?_insert ⟨m.1, _⟩ m.2 _ _ _

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome :=
  Raw₀.contains_eq_isSome_findEntry? ⟨m.1, _⟩ m.2

theorem findEntry?_eq_some {a : α} {p : Σ a, β a} (h : m.findEntry? a = some p) : p.1 == a :=
  Raw₀.findEntry?_eq_some ⟨m.1, _⟩ _ _ h

end

end MyLean.DHashMap
