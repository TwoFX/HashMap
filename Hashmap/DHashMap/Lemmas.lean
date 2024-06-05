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

section empty

@[simp]
theorem Raw₀.buckets_empty {c} {i : Nat} {h} : (empty c : Raw₀ α β).1.buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem Raw.buckets_empty {c} {i : Nat} {h} : (empty c : Raw α β).buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem Raw.buckets_emptyc {i : Nat} {h} : (∅ : Raw α β).buckets[i]'h = AssocList.nil :=
  buckets_empty

@[simp]
theorem buckets_empty {c} {i : Nat} {h} : (empty c : DHashMap α β).1.buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem buckets_emptyc {i : Nat} {h} : (∅ : DHashMap α β).1.buckets[i]'h = AssocList.nil :=
  buckets_empty

end empty

namespace Raw₀

variable (m : Raw₀ α β) (h : m.1.WF)

@[simp]
theorem findEntry?_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).findEntry? a = none := by
  simp [findEntry?]

@[simp]
theorem findConst?_empty {β : Type v} {a : α} {c : Nat} : (empty c : Raw₀ α (fun _ => β)).findConst? a = none := by
  simp [findConst?]

theorem findEntry?_insertB (a k : α) (b : β a) :
    (m.insertB a b).1.findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_findEntry? h.out.insertB, findEntry?_eq_findEntry? h.out,
    List.findEntry?_of_perm h.out.insertB.distinct (toListModel_insertB h.out),
    List.findEntry?_insertEntry]

theorem findEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).findEntry? k = bif a == k then some ⟨a, b⟩ else m.findEntry? k := by
  rw [findEntry?_eq_findEntry? h.out.insert, findEntry?_eq_findEntry? h.out,
    List.findEntry?_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.findEntry?_insertEntry]

theorem findConst?_insertB {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (a k : α) (b : β) :
    (m.insertB a b).1.findConst? k = bif a == k then some b else m.findConst? k := by
  rw [findConst?_eq_findValue? h.out.insertB, findConst?_eq_findValue? h.out,
    List.findValue?_of_perm h.out.insertB.distinct (toListModel_insertB h.out),
    List.findValue?_insertEntry]

theorem findConst?_insert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (a k : α) (b : β) :
    (m.insert a b).findConst? k = bif a == k then some b else m.findConst? k := by
  rw [findConst?_eq_findValue? h.out.insert, findConst?_eq_findValue? h.out,
    List.findValue?_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.findValue?_insertEntry]

theorem findConst?_congr {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {a b : α} (hab : a == b) :
    m.findConst? a = m.findConst? b := by
  rw [findConst?_eq_findValue? h.out, findConst?_eq_findValue? h.out, List.findValue?_eq_of_beq hab]

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).contains a = false := by
  simp [contains]

theorem contains_insertB (a k : α) (b : β a) : (m.insertB a b).1.contains k = ((a == k) || m.contains k) := by
  rw [contains_eq_containsKey h.out.insertB, contains_eq_containsKey h.out,
    List.containsKey_of_perm h.out.insertB.distinct (toListModel_insertB h.out),
    List.containsKey_insertEntry]

theorem contains_insert (a k : α) (b : β a) : (m.insert a b).contains k = ((a == k) || m.contains k) := by
  rw [contains_eq_containsKey h.out.insert, contains_eq_containsKey h.out,
    List.containsKey_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.containsKey_insertEntry]

theorem contains_eq_isSome_findEntry? {a : α} : m.contains a = (m.findEntry? a).isSome := by
  rw [findEntry?_eq_findEntry? h.out, contains_eq_containsKey h.out, List.containsKey_eq_isSome_findEntry?]

theorem findEntry?_eq_some (a : α) (p : Σ a, β a) (h : m.findEntry? a = some p) : p.1 == a :=
  AssocList.findEntry?_eq_some h

theorem mem_values_iff_exists_findConst?_eq_some {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {v : β} :
    v ∈ m.1.values ↔ ∃ k, m.findConst? k = some v := by
  rw [mem_values_iff_mem_values_toListModel, List.mem_values_iff_exists_findValue?_eq_some h.out.distinct]
  simp only [findConst?_eq_findValue? h.out]

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : Raw₀ α (fun _ => β)).1.values = [] := by
  simpa using Raw.values_perm_values_toListModel (m := (empty c : Raw₀ α (fun _ => β)).1)

theorem mem_values_insertB {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {a : α} {b v : β} :
    v ∈ (m.insertB a b).1.1.values ↔ b = v ∨ ∃ k, (a == k) = false ∧ m.findConst? k = some v := by
  rw [mem_values_iff_mem_values_toListModel, List.mem_values_of_perm h.out.insertB.distinct (toListModel_insertB h.out),
    List.mem_values_insertEntry h.out.distinct]
  simp only [findConst?_eq_findValue? h.out]

theorem mem_values_insert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {a : α} {b v : β} :
    v ∈ (m.insert a b).1.values ↔ b = v ∨ ∃ k, (a == k) = false ∧ m.findConst? k = some v := by
  rw [mem_values_iff_mem_values_toListModel, List.mem_values_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.mem_values_insertEntry h.out.distinct]
  simp only [findConst?_eq_findValue? h.out]

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

end

end MyLean.DHashMap
