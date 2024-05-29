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
theorem findEntry?_empty {a : α} {c : Nat} : (empty c : Raw α β).findEntry? a = none := by
  simp [findEntry?]

@[simp]
theorem findEntry?_emptyc {a : α} : (∅ : Raw α β).findEntry? a = none := by
  simp [findEntry?]

@[simp]
theorem find?_empty {a : α} {c : Nat} : (empty c : Raw α β).find? a = none := by
  simp [find?]

@[simp]
theorem find?_emptyc {a : α} : (∅ : Raw α β).find? a = none := by
  simp [find?]

theorem findEntry?_insert {a k : α} {b : β} :
    (m.insert a b).findEntry? k = bif a == k then some (a, b) else m.findEntry? k := by
  simp [findEntry?, insert, DHashMap.Raw.findEntry?_insert _ h, apply_bif (Option.map Sigma.toProd)]

theorem find?_insert {a k : α} {b : β} :
    (m.insert a b).find? k = bif a == k then some b else m.find? k := by
  simp [find?, insert, DHashMap.Raw.findConst?_insert _ h]

theorem find?_congr {a b : α} (hab : a == b) : m.find? a = m.find? b := by
  simp [find?, DHashMap.Raw.findConst?_congr _ h hab]

end Raw

section

variable (m : HashMap α β)

@[simp] theorem inner_emptyc : (∅ : HashMap α β).inner = ∅ := rfl
@[simp] theorem inner_empty {c : Nat} : (empty c : HashMap α β).inner = DHashMap.empty c := rfl

@[simp]
theorem findEntry?_empty {a : α} {c : Nat} : (empty c : HashMap α β).findEntry? a = none := by
  simp [findEntry?]

@[simp]
theorem findEntry?_emptyc {a : α} : (∅ : HashMap α β).findEntry? a = none := by
  simp [findEntry?]

@[simp]
theorem find?_empty {a : α} {c : Nat} : (empty c : HashMap α β).find? a = none := by
  simp [find?]

@[simp]
theorem find?_emptyc {a : α} : (∅ : HashMap α β).find? a = none := by
  simp [find?]

theorem findEntry?_insert {a k : α} {b : β} :
    (m.insert a b).findEntry? k = bif a == k then some (a, b) else m.findEntry? k := by
  simp [findEntry?, insert, DHashMap.findEntry?_insert, apply_bif (Option.map Sigma.toProd)]

theorem find?_insert {a k : α} {b : β} :
    (m.insert a b).find? k = bif a == k then some b else m.find? k := by
  simp [find?, insert, DHashMap.findConst?_insert]

end

end MyLean.HashMap
