/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.HashMap.Lemmas
import Hashmap.HashSet.Basic

set_option autoImplicit false

universe u v

variable {α : Type u} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace MyLean.HashSet

namespace Raw

variable (m : Raw α) (h : m.WF)

@[simp] theorem inner_emptyc : (∅ : Raw α).inner = ∅ := rfl
@[simp] theorem inner_empty {c : Nat} : (empty c : Raw α).inner = HashMap.Raw.empty c := rfl

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw α).contains a = false := by
  simp [contains]

@[simp]
theorem contains_emptyc {a : α} : (∅ : Raw α).contains a = false := by
  simp [contains]

theorem contains_insert {a k : α} : (m.insert a).contains k = ((a == k) || m.contains k) := by
  simp [contains, insert, HashMap.Raw.contains_insert _ h]

end Raw

section

variable (m : HashSet α)

@[simp] theorem inner_emptyc : (∅ : HashSet α).inner = ∅ := rfl
@[simp] theorem inner_empty {c : Nat} : (empty c : HashSet α).inner = HashMap.empty c := rfl

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : HashSet α).contains a = false := by
  simp [contains]

@[simp]
theorem contains_emptyc {a : α} : (∅ : Raw α).contains a = false := by
  simp [contains]

theorem contains_insert {a k : α} : (m.insert a).contains k = ((a == k) || m.contains k) := by
  simp [contains, insert, HashMap.contains_insert]

end

end MyLean.HashSet
