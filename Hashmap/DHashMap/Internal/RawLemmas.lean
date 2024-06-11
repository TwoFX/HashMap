/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Internal.WF

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

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw₀ α β).1.isEmpty := by
  rw [Raw.isEmpty_eq_isEmpty wfImp_empty, toListModel_buckets_empty, List.isEmpty_nil]

@[simp]
theorem isEmpty_insertB {a : α} {b : β a} : (m.insertB a b).1.1.isEmpty = false := by
  rw [Raw.isEmpty_eq_isEmpty h.out.insertB, (toListModel_insertB h.out).isEmpty_eq, List.isEmpty_insertEntry]

@[simp]
theorem isEmpty_insert {a : α} {b : β a} : (m.insert a b).1.isEmpty = false := by
  rw [Raw.isEmpty_eq_isEmpty h.out.insert, (toListModel_insert h.out).isEmpty_eq, List.isEmpty_insertEntry]

theorem findEntry?_of_isEmpty {a : α} (h' : m.1.isEmpty = true) : m.findEntry? a = none := by
  simp_all [findEntry?_eq_findEntry? h.out, Raw.isEmpty_eq_isEmpty h.out, List.isEmpty_iff]

theorem findConst?_of_isEmpty {a : α} {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (h' : m.1.isEmpty = true) :
    m.findConst? a = none := by
  simp_all [findConst?_eq_findValue? h.out, Raw.isEmpty_eq_isEmpty h.out, List.isEmpty_iff]

theorem contains_of_isEmpty {a : α} (h' : m.1.isEmpty = true) : m.contains a = false := by
  simp_all [contains_eq_containsKey h.out, Raw.isEmpty_eq_isEmpty h.out, List.isEmpty_iff]

theorem isEmpty_iff_size_eq_zero : m.1.isEmpty ↔ m.1.size = 0 := by
  simp [Raw.isEmpty]

end Raw₀

end MyLean.DHashMap
