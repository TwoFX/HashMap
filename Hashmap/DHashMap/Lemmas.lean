/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Internal.RawLemmas

set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace MyLean.DHashMap

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

theorem findConst?_congr {β : Type v} (m : Raw α (fun _ => β)) (h : m.WF) {a b : α} (hab : a == b) :
    m.findConst? a = m.findConst? b := by
  rw [findConst?_eq h, findConst?_eq h, Raw₀.findConst?_congr ⟨m, _⟩ h hab]

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw α β).contains a = false := by
  rw [empty_eq, contains_eq WF.empty₀, Raw₀.contains_empty]

@[simp]
theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false :=
  contains_empty

theorem contains_insert {a k : α} {b : β a} : (m.insert a b).contains k = ((a == k) || m.contains k) := by
  rw [insert_eq h, contains_eq h, contains_eq h.insert₀, Raw₀.contains_insert ⟨m, _⟩ h]

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome := by
  rw [contains_eq h, findEntry?_eq h, Raw₀.contains_eq_isSome_findEntry? ⟨m, _⟩ h]

theorem mem_values_iff_exists_findConst?_eq_some {β : Type v} (m : Raw α (fun _ => β)) (h : m.WF) {v : β} :
    v ∈ m.values ↔ ∃ k, m.findConst? k = some v := by
  rw [Raw₀.mem_values_iff_exists_findConst?_eq_some ⟨m, h.size_buckets_pos⟩ h]
  simp only [findConst?_eq h]

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : Raw α (fun _ => β)).values = [] :=
  Raw₀.values_empty

@[simp]
theorem values_emptyc {β : Type v} : (∅ : Raw α (fun _ => β)).values = [] :=
  values_empty

theorem mem_values_insert {β : Type v} {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {b v : β} :
    v ∈ (m.insert a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ m.findConst? k = some v := by
  rw [insert_eq h, Raw₀.mem_values_insert ⟨m, h.size_buckets_pos⟩ h]
  simp only [findConst?_eq h]

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α β).isEmpty :=
  Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_insertB {a : α} {b : β a} : (m.insertB a b).1.isEmpty = false := by
  rw [insertB_eq h, Raw₀.isEmpty_insertB ⟨m, _⟩ h]

@[simp]
theorem isEmpty_insert {a : α} {b : β a} : (m.insert a b).isEmpty = false := by
  rw [insert_eq h, Raw₀.isEmpty_insert ⟨m, _⟩ h]

theorem findEntry?_of_isEmpty {a : α} (h' : m.isEmpty = true) : m.findEntry? a = none := by
  rw [findEntry?_eq h, Raw₀.findEntry?_of_isEmpty ⟨m, _⟩ h h']

theorem findConst?_of_isEmpty {a : α} {β : Type v} {m : Raw α (fun _ => β)} (h : m.WF) (h' : m.isEmpty = true) :
    m.findConst? a = none := by
  rw [findConst?_eq h, Raw₀.findConst?_of_isEmpty ⟨m, _⟩ h h']

theorem contains_of_isEmpty {a : α} (h' : m.isEmpty = true) : m.contains a = false := by
  rw [contains_eq h, Raw₀.contains_of_isEmpty ⟨m, _⟩ h h']

theorem isEmpty_iff_size_eq_zero : m.isEmpty ↔ m.size = 0 := by
  simp [isEmpty]

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

theorem findConst?_congr {β : Type v} (m : DHashMap α (fun _ => β)) {a b : α} (hab : a == b) :
    m.findConst? a = m.findConst? b :=
  Raw₀.findConst?_congr ⟨m.1, _⟩ m.2 hab

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : DHashMap α β).contains a = false :=
  Raw₀.contains_empty

@[simp]
theorem contains_emptyc {a : α} : (∅ : DHashMap α β).contains a = false :=
  Raw₀.contains_empty

theorem contains_insert {a k : α} {b : β a} : (m.insert a b).contains k = ((a == k) || m.contains k) :=
  Raw₀.contains_insert ⟨m.1, _⟩ m.2 _ _ _

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome :=
  Raw₀.contains_eq_isSome_findEntry? ⟨m.1, _⟩ m.2

theorem findEntry?_eq_some {a : α} {p : Σ a, β a} (h : m.findEntry? a = some p) : p.1 == a :=
  Raw₀.findEntry?_eq_some ⟨m.1, _⟩ _ _ h

theorem mem_values_iff_exists_findConst?_eq_some {β : Type v} (m : DHashMap α (fun _ => β)) {v : β} :
    v ∈ m.values ↔ ∃ k, m.findConst? k = some v :=
  Raw₀.mem_values_iff_exists_findConst?_eq_some ⟨m.1, _⟩ m.2

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : DHashMap α (fun _ => β)).values = [] :=
  Raw₀.values_empty

@[simp]
theorem values_emptyc {β : Type v} : (∅ : DHashMap α (fun _ => β)).values = [] :=
  values_empty

theorem mem_values_insert {β : Type v} {m : DHashMap α (fun _ => β)} {a : α} {b v : β} :
    v ∈ (m.insert a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ m.findConst? k = some v :=
  Raw₀.mem_values_insert ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_empty {c} : (empty c : DHashMap α β).isEmpty :=
  Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : DHashMap α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_insertB {a : α} {b : β a} : (m.insertB a b).1.isEmpty = false :=
  Raw₀.isEmpty_insertB ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_insert {a : α} {b : β a} : (m.insert a b).isEmpty = false :=
  Raw₀.isEmpty_insert ⟨m.1, _⟩ m.2

theorem findEntry?_of_isEmpty {a : α} (h : m.isEmpty = true) : m.findEntry? a = none :=
  Raw₀.findEntry?_of_isEmpty ⟨m.1, _⟩ m.2 h

theorem findConst?_of_isEmpty {a : α} {β : Type v} {m : DHashMap α (fun _ => β)} (h : m.isEmpty = true) :
    m.findConst? a = none :=
  Raw₀.findConst?_of_isEmpty ⟨m.1, _⟩ m.2 h

theorem contains_of_isEmpty {a : α} (h : m.isEmpty = true) : m.contains a = false :=
  Raw₀.contains_of_isEmpty ⟨m.1, _⟩ m.2 h

theorem isEmpty_iff_size_eq_zero : m.isEmpty ↔ m.size = 0 :=
  Raw₀.isEmpty_iff_size_eq_zero ⟨m.1, m.2.size_buckets_pos⟩

end

end MyLean.DHashMap
