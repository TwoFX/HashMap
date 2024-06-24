/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

open List

-- TODO

theorem List.exists_of_set' {n : Nat} {a' : α} {l : List α} (h : n < l.length) :
    ∃ l₁ l₂, l = l₁ ++ l.get ⟨n, h⟩ :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  induction n generalizing a' l
  · cases l
    · simp at h
    · next h t => refine ⟨[], t, by simp⟩
  · next n ih =>
    cases l
    · simp at h; omega
    · next a t =>
      simp only [length_cons, Nat.succ_eq_add_one] at h
      obtain ⟨t₁, t₂, ⟨ht₁, ht₂, ht₃⟩⟩ := ih (Nat.succ_lt_succ_iff.1 h)
      exact ⟨a :: t₁, t₂, by simpa [ht₁, ht₂] using ht₁ ▸ ht₃⟩

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

-- From mathlib
theorem List.isEmpty_iff {l : List α} : l.isEmpty ↔ l = [] := by
  cases l <;> simp

theorem List.isEmpty_iff_length_eq_zero {l : List α} : l.isEmpty ↔ l.length = 0 := by
  rw [isEmpty_iff, length_eq_zero]

theorem List.get?_set_lt {n m : Nat} {l : List α} {a : α} (h : n < m) :
    (l.set n a).get? m = l.get? m := by
  induction l generalizing a n m
  · simp
  · next a t ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    cases n
    · simp
    · simpa using ih (by omega)

-- From batteries
theorem List.drop_set_of_lt (a : α) {n m : Nat} (l : List α)
    (hnm : n < m) : List.drop m (l.set n a) = List.drop m l := by
  apply List.ext
  intro k
  simp only [get?_drop]
  exact List.get?_set_lt (by omega)
