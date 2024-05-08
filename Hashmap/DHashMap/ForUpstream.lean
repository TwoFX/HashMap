
/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Batteries.Data.List.Perm

open List

-- TODO
theorem List.perm_append_comm_assoc (l₁ l₂ l₃ : List α) : l₁ ++ (l₂ ++ l₃) ~ l₂ ++ (l₁ ++ l₃) := by
  simpa only [List.append_assoc] using perm_append_comm.append_right _

-- TODO: this is just about arrays
theorem Array.exists_of_update (self : Array α) (i d h) :
    ∃ l₁ l₂, self.data = l₁ ++ self[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (self.uset i d h).data = l₁ ++ d :: l₂ := by
  simp [Array.getElem_eq_data_get]; exact List.exists_of_set' _

-- TODO
theorem List.length_le_append_right {l₁ l₂ : List α} : l₁.length ≤ (l₁ ++ l₂).length := by
  simpa using Nat.le_add_right _ _

-- TODO
theorem List.length_le_append_left {l₁ l₂ : List α} : l₂.length ≤ (l₁ ++ l₂).length := by
  simpa using Nat.le_add_left _ _

-- TODO
theorem List.get_eq_get_append_right {l₁ : List α} (l₂ : List α) {n : Fin l₁.length} :
    l₁.get n = (l₁ ++ l₂).get (n.castLE length_le_append_right) := by
  rw [get_append]; rfl

-- TODO
theorem List.get_eq_get_append_left (l₁ : List α) {l₂ : List α} {n : Fin l₂.length} :
    l₂.get n = (l₁ ++ l₂).get ((n.addNat l₁.length).cast (by simp [Nat.add_comm l₂.length])) := by
  rw [get_append_right]
  · simp
  · simpa using Nat.le_add_left _ _
  · simp

-- TODO
theorem List.get_eq_get_cons (a : α) {l : List α} {n : Fin l.length} :
    l.get n = (a :: l).get ((n.addNat 1).cast (by simp)) := by
  erw [get_cons_succ]

-- TODO
theorem List.get_congr {l₁ l₂ : List α} {n : Fin l₁.length} (h : l₁ = l₂) :
    l₁.get n = l₂.get (n.cast (h ▸ rfl)) := by
  cases h; rfl

-- TODO
theorem Nat.lt_of_eq_of_lt {n m k : Nat} : n = m → m < k → n < k :=
  fun h₁ h₂ => h₁ ▸ h₂
