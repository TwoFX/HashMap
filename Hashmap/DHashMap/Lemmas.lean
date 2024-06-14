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
theorem getEntry?_empty {a : α} {c : Nat} : (empty c : Raw α β).getEntry? a = none := by
  rw [empty_eq, getEntry?_eq WF.empty₀, Raw₀.getEntry?_empty]

@[simp]
theorem getEntry?_emptyc {a : α} : (∅ : Raw α β).getEntry? a = none :=
  getEntry?_empty

@[simp]
theorem Const.get?_empty {β : Type v} {a : α} {c : Nat} : Const.get? (empty c : Raw α (fun _ => β)) a = none := by
  rw [empty_eq, Const.get?_eq WF.empty₀, Raw₀.Const.get?_empty]

@[simp]
theorem getConst?_emptyc {β : Type v} {a : α} : Const.get? (∅ : Raw α (fun _ => β)) a = none :=
  Const.get?_empty

theorem getEntry?_insert {a k : α} {b : β a} :
    (m.insert a b).getEntry? k = bif a == k then some ⟨a, b⟩ else m.getEntry? k := by
  rw [insert_eq h, getEntry?_eq h, getEntry?_eq h.insert₀, Raw₀.getEntry?_insert ⟨m, _⟩ h]

theorem Const.get?_insert {β : Type v} (m : Raw α (fun _ => β)) (h : m.WF) (a k : α) (b : β) :
    Const.get? (m.insert a b) k = bif a == k then some b else Const.get? m k := by
  rw [insert_eq h, Const.get?_eq h, Const.get?_eq h.insert₀, Raw₀.Const.get?_insert ⟨m, _⟩ h]

theorem Const.get?_congr {β : Type v} (m : Raw α (fun _ => β)) (h : m.WF) {a b : α} (hab : a == b) :
    Const.get? m a = Const.get? m b := by
  rw [Const.get?_eq h, Const.get?_eq h, Raw₀.Const.get?_congr ⟨m, _⟩ h hab]

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw α β).contains a = false := by
  rw [empty_eq, contains_eq WF.empty₀, Raw₀.contains_empty]

@[simp]
theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false :=
  contains_empty

theorem contains_insert {a k : α} {b : β a} : (m.insert a b).contains k = ((a == k) || m.contains k) := by
  rw [insert_eq h, contains_eq h, contains_eq h.insert₀, Raw₀.contains_insert ⟨m, _⟩ h]

theorem contains_eq_isSome_getEntry? {a : α} : m.contains a = (m.getEntry? a).isSome := by
  rw [contains_eq h, getEntry?_eq h, Raw₀.contains_eq_isSome_getEntry? ⟨m, _⟩ h]

theorem Const.mem_values_iff_exists_get?_eq_some {β : Type v} (m : Raw α (fun _ => β)) (h : m.WF) {v : β} :
    v ∈ m.values ↔ ∃ k, Const.get? m k = some v := by
  rw [Raw₀.Const.mem_values_iff_exists_get?_eq_some ⟨m, h.size_buckets_pos⟩ h]
  simp only [Const.get?_eq h]

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : Raw α (fun _ => β)).values = [] :=
  Raw₀.values_empty

@[simp]
theorem values_emptyc {β : Type v} : (∅ : Raw α (fun _ => β)).values = [] :=
  values_empty

theorem mem_values_insert {β : Type v} {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {b v : β} :
    v ∈ (m.insert a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ Const.get? m k = some v := by
  rw [insert_eq h, Raw₀.mem_values_insert ⟨m, h.size_buckets_pos⟩ h]
  simp only [Const.get?_eq h]

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α β).isEmpty :=
  Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_containsThenInsert {a : α} {b : β a} : (m.containsThenInsert a b).1.isEmpty = false := by
  rw [containsThenInsert_eq h, Raw₀.isEmpty_containsThenInsert ⟨m, _⟩ h]

@[simp]
theorem isEmpty_insert {a : α} {b : β a} : (m.insert a b).isEmpty = false := by
  rw [insert_eq h, Raw₀.isEmpty_insert ⟨m, _⟩ h]

theorem getEntry?_of_isEmpty {a : α} (h' : m.isEmpty = true) : m.getEntry? a = none := by
  rw [getEntry?_eq h, Raw₀.getEntry?_of_isEmpty ⟨m, _⟩ h h']

theorem Const.get?_of_isEmpty {a : α} {β : Type v} {m : Raw α (fun _ => β)} (h : m.WF) (h' : m.isEmpty = true) :
    Const.get? m a = none := by
  rw [Const.get?_eq h, Raw₀.Const.get?_of_isEmpty ⟨m, _⟩ h h']

theorem contains_of_isEmpty {a : α} (h' : m.isEmpty = true) : m.contains a = false := by
  rw [contains_eq h, Raw₀.contains_of_isEmpty ⟨m, _⟩ h h']

theorem isEmpty_iff_size_eq_zero : m.isEmpty ↔ m.size = 0 := by
  simp [isEmpty]

end Raw

section

variable (m : DHashMap α β)

@[simp]
theorem getEntry?_empty {a : α} {c : Nat} : (empty c : DHashMap α β).getEntry? a = none :=
  Raw₀.getEntry?_empty

@[simp]
theorem getEntry?_emptyc {a : α} : (∅ : DHashMap α β).getEntry? a = none :=
  Raw₀.getEntry?_empty

@[simp]
theorem Const.get?_empty {β : Type v} {a : α} {c : Nat} : Const.get? (empty c : DHashMap α (fun _ => β)) a = none :=
  Raw₀.Const.get?_empty

@[simp]
theorem Const.get?_emptyc {β : Type v} {a : α} : Const.get? (∅ : DHashMap α (fun _ => β)) a = none :=
  Raw₀.Const.get?_empty

theorem getEntry?_insert (a k : α) (b : β a) :
    (m.insert a b).getEntry? k = bif a == k then some ⟨a, b⟩ else m.getEntry? k :=
  Raw₀.getEntry?_insert ⟨m.1, _⟩ m.2 a k b

theorem Const.get?_insert {β : Type v} (m : DHashMap α (fun _ => β)) (a k : α) (b : β) :
    Const.get? (m.insert a b) k = bif a == k then some b else Const.get? m k :=
  Raw₀.Const.get?_insert ⟨m.1, _⟩ m.2 ..

theorem Const.get?_congr {β : Type v} (m : DHashMap α (fun _ => β)) {a b : α} (hab : a == b) :
    Const.get? m a = Const.get? m b :=
  Raw₀.Const.get?_congr ⟨m.1, _⟩ m.2 hab

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : DHashMap α β).contains a = false :=
  Raw₀.contains_empty

@[simp]
theorem contains_emptyc {a : α} : (∅ : DHashMap α β).contains a = false :=
  Raw₀.contains_empty

theorem contains_insert {a k : α} {b : β a} : (m.insert a b).contains k = ((a == k) || m.contains k) :=
  Raw₀.contains_insert ⟨m.1, _⟩ m.2 _ _ _

theorem contains_eq_isSome_getEntry? {a : α} : m.contains a = (m.getEntry? a).isSome :=
  Raw₀.contains_eq_isSome_getEntry? ⟨m.1, _⟩ m.2

theorem getEntry?_eq_some {a : α} {p : Σ a, β a} (h : m.getEntry? a = some p) : p.1 == a :=
  Raw₀.getEntry?_eq_some ⟨m.1, _⟩ _ _ h

theorem Const.mem_values_iff_exists_get?_eq_some {β : Type v} (m : DHashMap α (fun _ => β)) {v : β} :
    v ∈ m.values ↔ ∃ k, Const.get? m k = some v :=
  Raw₀.Const.mem_values_iff_exists_get?_eq_some ⟨m.1, _⟩ m.2

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : DHashMap α (fun _ => β)).values = [] :=
  Raw₀.values_empty

@[simp]
theorem values_emptyc {β : Type v} : (∅ : DHashMap α (fun _ => β)).values = [] :=
  values_empty

theorem mem_values_insert {β : Type v} {m : DHashMap α (fun _ => β)} {a : α} {b v : β} :
    v ∈ (m.insert a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ Const.get? m k = some v :=
  Raw₀.mem_values_insert ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_empty {c} : (empty c : DHashMap α β).isEmpty :=
  Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : DHashMap α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_containsThenInsert {a : α} {b : β a} : (m.containsThenInsert a b).1.isEmpty = false :=
  Raw₀.isEmpty_containsThenInsert ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_insert {a : α} {b : β a} : (m.insert a b).isEmpty = false :=
  Raw₀.isEmpty_insert ⟨m.1, _⟩ m.2

theorem getEntry?_of_isEmpty {a : α} (h : m.isEmpty = true) : m.getEntry? a = none :=
  Raw₀.getEntry?_of_isEmpty ⟨m.1, _⟩ m.2 h

theorem Const.get?_of_isEmpty {a : α} {β : Type v} {m : DHashMap α (fun _ => β)} (h : m.isEmpty = true) :
    Const.get? m a = none :=
  Raw₀.Const.get?_of_isEmpty ⟨m.1, _⟩ m.2 h

theorem contains_of_isEmpty {a : α} (h : m.isEmpty = true) : m.contains a = false :=
  Raw₀.contains_of_isEmpty ⟨m.1, _⟩ m.2 h

theorem isEmpty_iff_size_eq_zero : m.isEmpty ↔ m.size = 0 :=
  Raw₀.isEmpty_iff_size_eq_zero ⟨m.1, m.2.size_buckets_pos⟩

end

end MyLean.DHashMap
