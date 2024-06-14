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
theorem getEntry?_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).getEntry? a = none := by
  simp [getEntry?]

@[simp]
theorem Const.get?_empty {β : Type v} {a : α} {c : Nat} : Const.get? (empty c : Raw₀ α (fun _ => β)) a = none := by
  simp [Const.get?]

theorem getEntry?_containsThenInsert (a k : α) (b : β a) :
    (m.containsThenInsert a b).1.getEntry? k = bif a == k then some ⟨a, b⟩ else m.getEntry? k := by
  rw [getEntry?_eq_getEntry? h.out.containsThenInsert, getEntry?_eq_getEntry? h.out,
    List.getEntry?_of_perm h.out.containsThenInsert.distinct (toListModel_containsThenInsert h.out),
    List.getEntry?_insertEntry]

theorem getEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).getEntry? k = bif a == k then some ⟨a, b⟩ else m.getEntry? k := by
  rw [getEntry?_eq_getEntry? h.out.insert, getEntry?_eq_getEntry? h.out,
    List.getEntry?_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.getEntry?_insertEntry]

theorem Const.get?_containsThenInsert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (a k : α) (b : β) :
    Const.get? (m.containsThenInsert a b).1 k = bif a == k then some b else Const.get? m k := by
  rw [Const.get?_eq_getValue? h.out.containsThenInsert, Const.get?_eq_getValue? h.out,
    List.getValue?_of_perm h.out.containsThenInsert.distinct (toListModel_containsThenInsert h.out),
    List.getValue?_insertEntry]

theorem Const.get?_insert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (a k : α) (b : β) :
    Const.get? (m.insert a b) k = bif a == k then some b else Const.get? m k := by
  rw [Const.get?_eq_getValue? h.out.insert, Const.get?_eq_getValue? h.out,
    List.getValue?_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.getValue?_insertEntry]

theorem Const.get?_congr {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {a b : α} (hab : a == b) :
    Const.get? m a = Const.get? m b := by
  rw [Const.get?_eq_getValue? h.out, Const.get?_eq_getValue? h.out, List.getValue?_eq_of_beq hab]

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).contains a = false := by
  simp [contains]

theorem contains_containsThenInsert (a k : α) (b : β a) : (m.containsThenInsert a b).1.contains k = ((a == k) || m.contains k) := by
  rw [contains_eq_containsKey h.out.containsThenInsert, contains_eq_containsKey h.out,
    List.containsKey_of_perm h.out.containsThenInsert.distinct (toListModel_containsThenInsert h.out),
    List.containsKey_insertEntry]

theorem contains_insert (a k : α) (b : β a) : (m.insert a b).contains k = ((a == k) || m.contains k) := by
  rw [contains_eq_containsKey h.out.insert, contains_eq_containsKey h.out,
    List.containsKey_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.containsKey_insertEntry]

theorem contains_eq_isSome_getEntry? {a : α} : m.contains a = (m.getEntry? a).isSome := by
  rw [getEntry?_eq_getEntry? h.out, contains_eq_containsKey h.out, List.containsKey_eq_isSome_getEntry?]

theorem getEntry?_eq_some (a : α) (p : Σ a, β a) (h : m.getEntry? a = some p) : p.1 == a :=
  AssocList.getEntry?_eq_some h

theorem Const.mem_values_iff_exists_get?_eq_some {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {v : β} :
    v ∈ m.1.values ↔ ∃ k, Const.get? m k = some v := by
  rw [mem_values_iff_mem_values_toListModel, List.mem_values_iff_exists_getValue?_eq_some h.out.distinct]
  simp only [Const.get?_eq_getValue? h.out]

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : Raw₀ α (fun _ => β)).1.values = [] := by
  simpa using Raw.values_perm_values_toListModel (m := (empty c : Raw₀ α (fun _ => β)).1)

theorem mem_values_containsThenInsert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {a : α} {b v : β} :
    v ∈ (m.containsThenInsert a b).1.1.values ↔ b = v ∨ ∃ k, (a == k) = false ∧ Const.get? m k = some v := by
  rw [mem_values_iff_mem_values_toListModel, List.mem_values_of_perm h.out.containsThenInsert.distinct (toListModel_containsThenInsert h.out),
    List.mem_values_insertEntry h.out.distinct]
  simp only [Const.get?_eq_getValue? h.out]

theorem mem_values_insert {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {a : α} {b v : β} :
    v ∈ (m.insert a b).1.values ↔ b = v ∨ ∃ k, (a == k) = false ∧ Const.get? m k = some v := by
  rw [mem_values_iff_mem_values_toListModel, List.mem_values_of_perm h.out.insert.distinct (toListModel_insert h.out),
    List.mem_values_insertEntry h.out.distinct]
  simp only [Const.get?_eq_getValue? h.out]

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw₀ α β).1.isEmpty := by
  rw [Raw.isEmpty_eq_isEmpty wfImp_empty, toListModel_buckets_empty, List.isEmpty_nil]

@[simp]
theorem isEmpty_containsThenInsert {a : α} {b : β a} : (m.containsThenInsert a b).1.1.isEmpty = false := by
  rw [Raw.isEmpty_eq_isEmpty h.out.containsThenInsert, (toListModel_containsThenInsert h.out).isEmpty_eq, List.isEmpty_insertEntry]

@[simp]
theorem isEmpty_insert {a : α} {b : β a} : (m.insert a b).1.isEmpty = false := by
  rw [Raw.isEmpty_eq_isEmpty h.out.insert, (toListModel_insert h.out).isEmpty_eq, List.isEmpty_insertEntry]

theorem getEntry?_of_isEmpty {a : α} (h' : m.1.isEmpty = true) : m.getEntry? a = none := by
  simp_all [getEntry?_eq_getEntry? h.out, Raw.isEmpty_eq_isEmpty h.out, List.isEmpty_iff]

theorem Const.get?_of_isEmpty {a : α} {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF) (h' : m.1.isEmpty = true) :
    Const.get? m a = none := by
  simp_all [Const.get?_eq_getValue? h.out, Raw.isEmpty_eq_isEmpty h.out, List.isEmpty_iff]

theorem contains_of_isEmpty {a : α} (h' : m.1.isEmpty = true) : m.contains a = false := by
  simp_all [contains_eq_containsKey h.out, Raw.isEmpty_eq_isEmpty h.out, List.isEmpty_iff]

theorem isEmpty_iff_size_eq_zero : m.1.isEmpty ↔ m.1.size = 0 := by
  simp [Raw.isEmpty]

end Raw₀

end MyLean.DHashMap
