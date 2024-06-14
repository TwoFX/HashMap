/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Lemmas
import Hashmap.HashMap.Basic

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace MyLean.HashMap

namespace Raw

variable (m : Raw α β) (h : m.WF)

@[simp] theorem inner_emptyc : (∅ : Raw α β).inner = ∅ := rfl
@[simp] theorem inner_empty {c : Nat} : (empty c : Raw α β).inner = DHashMap.Raw.empty c := rfl

@[simp]
theorem getEntry?_empty {a : α} {c : Nat} : (empty c : Raw α β).getEntry? a = none := by
  simp [getEntry?]

@[simp]
theorem getEntry?_emptyc {a : α} : (∅ : Raw α β).getEntry? a = none := by
  simp [getEntry?]

@[simp]
theorem get?_empty {a : α} {c : Nat} : (empty c : Raw α β).get? a = none := by
  simp [get?]

@[simp]
theorem get?_emptyc {a : α} : (∅ : Raw α β).get? a = none := by
  simp [get?]

theorem getEntry?_insert {a k : α} {b : β} :
    (m.insert a b).getEntry? k = bif a == k then some (a, b) else m.getEntry? k := by
  simp [getEntry?, insert, DHashMap.Raw.getEntry?_insert _ h, apply_bif (Option.map Sigma.toProd)]

theorem get?_insert {a k : α} {b : β} :
    (m.insert a b).get? k = bif a == k then some b else m.get? k := by
  simp [get?, insert, DHashMap.Raw.Const.get?_insert _ h]

theorem get?_congr {a b : α} (hab : a == b) : m.get? a = m.get? b := by
  simp [get?, DHashMap.Raw.Const.get?_congr _ h hab]

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw α β).contains a = false := by
  simp [contains]

@[simp]
theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false := by
  simp [contains]

theorem contains_insert {a k : α} {b : β} : (m.insert a b).contains k = ((a == k) || m.contains k) := by
  simp [contains, insert, DHashMap.Raw.contains_insert _ h]

theorem mem_values_iff_exists_get?_eq_some {β : Type v} (m : Raw α β) (h : m.WF) {v : β} :
    v ∈ m.values ↔ ∃ k, m.get? k = some v := by
  simp [values, get?, DHashMap.Raw.Const.mem_values_iff_exists_get?_eq_some _ h]

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : Raw α β).values = [] := by
  simp [values]

@[simp]
theorem values_emptyc {β : Type v} : (∅ : Raw α β).values = [] := by
  simp [values]

theorem mem_values_insert {β : Type v} {m : Raw α β} (h : m.WF) {a : α} {b v : β} :
    v ∈ (m.insert a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ m.get? k = some v := by
  simp [values, get?, insert, DHashMap.Raw.mem_values_insert h]

end Raw

section

variable (m : HashMap α β)

@[simp] theorem inner_emptyc : (∅ : HashMap α β).inner = ∅ := rfl
@[simp] theorem inner_empty {c : Nat} : (empty c : HashMap α β).inner = DHashMap.empty c := rfl

@[simp]
theorem getEntry?_empty {a : α} {c : Nat} : (empty c : HashMap α β).getEntry? a = none := by
  simp [getEntry?]

@[simp]
theorem getEntry?_emptyc {a : α} : (∅ : HashMap α β).getEntry? a = none := by
  simp [getEntry?]

@[simp]
theorem get?_empty {a : α} {c : Nat} : (empty c : HashMap α β).get? a = none := by
  simp [get?]

@[simp]
theorem get?_emptyc {a : α} : (∅ : HashMap α β).get? a = none := by
  simp [get?]

theorem getEntry?_insert {a k : α} {b : β} :
    (m.insert a b).getEntry? k = bif a == k then some (a, b) else m.getEntry? k := by
  simp [getEntry?, insert, DHashMap.getEntry?_insert, apply_bif (Option.map Sigma.toProd)]

theorem get?_insert {a k : α} {b : β} :
    (m.insert a b).get? k = bif a == k then some b else m.get? k := by
  simp [get?, insert, DHashMap.Const.get?_insert]

theorem get?_congr {a b : α} (hab : a == b) : m.get? a = m.get? b := by
  simp [get?, DHashMap.Const.get?_congr _ hab]

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : HashMap α β).contains a = false := by
  simp [contains]

@[simp]
theorem contains_emptyc {a : α} : (∅ : HashMap α β).contains a = false := by
  simp [contains]

theorem contains_insert {a k : α} {b : β} : (m.insert a b).contains k = ((a == k) || m.contains k) := by
  simp [contains, insert, DHashMap.contains_insert]

theorem mem_values_iff_exists_get?_eq_some {β : Type v} (m : HashMap α β) {v : β} :
    v ∈ m.values ↔ ∃ k, m.get? k = some v := by
  simp [values, get?, DHashMap.Const.mem_values_iff_exists_get?_eq_some]

@[simp]
theorem values_empty {β : Type v} {c} : (empty c : HashMap α β).values = [] := by
  simp [values]

@[simp]
theorem values_emptyc {β : Type v} : (∅ : HashMap α β).values = [] := by
  simp [values]

theorem mem_values_insert {β : Type v} {m : HashMap α β} {a : α} {b v : β} :
    v ∈ (m.insert a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ m.get? k = some v := by
  simp [values, get?, insert, DHashMap.mem_values_insert]

end

end MyLean.HashMap
