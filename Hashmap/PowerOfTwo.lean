/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

-- Some wasted work because I didn't scroll to the very bottom of Bitwise/Lemmas.lean :(
-- But I think many of these statements are still interesting, and my approach is slighly more general

-- @[simp]
-- theorem Nat.testBit_pow_two {i j : Nat} : (2^i).testBit j = decide (i = j) := by
--   rw [Nat.testBit_to_div_mod]
--   rcases Nat.lt_trichotomy i j with (h|rfl|h)
--   · rw [Nat.div_eq_of_lt]
--     · simp_all; omega
--     · exact Nat.pow_lt_pow_of_lt Nat.one_lt_two h
--   · rw [Nat.div_self]
--     · simp
--     · exact Nat.pow_pos Nat.two_pos
--   · rw [Nat.pow_div (Nat.le_of_lt h) Nat.two_pos]
--     simp [Nat.ne_of_lt' h]
--     suffices (2 ^ (i - j)) % (2 ^ 1) = 0 by simp_all
--     rw [← Nat.dvd_iff_mod_eq_zero]
--     apply Nat.pow_dvd_pow
--     omega

-- @[simp]
-- theorem testBit_mul_two_zero {n : Nat} : (n * 2).testBit 0 = false := by
--   rw [Nat.testBit_zero]
--   simp

-- @[simp]
-- theorem testBit_mul_two_succ {n i : Nat} : (n * 2).testBit (i + 1) = n.testBit i := by
--   rw [Nat.testBit_succ]
--   simp

-- theorem testBit_mul_two_pow_lt {n k i : Nat} (hi : i < k) : (n * 2^k).testBit i = false := by
--   induction k generalizing i
--   · simp [Nat.not_lt_zero] at hi
--   · next m ih =>
--     rw [Nat.pow_succ, ← Nat.mul_assoc]
--     rcases i with (i|i)
--     · simp
--     · rw [testBit_mul_two_succ]
--       exact ih (Nat.succ_lt_succ_iff.1 hi)

-- @[simp]
-- theorem testBit_mul_two_pow_add {n k i : Nat} : (n * 2^k).testBit (i + k) = n.testBit i := by
--   induction k generalizing i
--   · simp
--   · next m ih =>
--     skip
--     rw [Nat.pow_succ, ← Nat.mul_assoc, ← Nat.add_assoc, testBit_mul_two_succ]
--     exact ih

-- #check BitVec

-- theorem testBit_div_two {n i : Nat} : n.testBit (i + 1) = (n / 2).testBit i := by
--   exact Nat.testBit_succ n i

-- @[simp]
-- theorem Nat.lt_one_iff {n : Nat} : n < 1 ↔ n = 0 := by
--   cases n <;> simp


-- theorem Nat.add_eq_xor_impl {n m k : Nat} (hn : n < 2^k) (hm : m < 2^k) (h : ∀ i, n.testBit i = false ∨ m.testBit i = false) :
--     n + m = n ^^^ m := by
--   induction k generalizing n m
--   · simp_all

-- theorem Nat.lt_pow_self {n : Nat} : n < 2 ^ n := by
--   induction n
--   · decide
--   · next n ih =>
--     exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ ih) (Nat.succ_le_of_lt (Nat.pow_lt_pow_succ Nat.one_lt_two))

-- theorem Nat.exists_lt_pow {n : Nat} : ∃ k, n < 2^k := by
--   induction n
--   · refine ⟨0, by decide⟩
--   · next n ih =>
--     obtain \<

-- theorem Nat.add_eq_xor {n m : Nat} (h : ∀ i, n.testBit i = false ∨ m.testBit i = false) :
--     n + m = n ^^^ m := by
--   have h₁ : n < 2 ^ (max n m) := Nat.lt_of_lt_of_le Nat.lt_pow_self (Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_max_left _ _))
--   have h₂ : m < 2 ^ (max n m) := Nat.lt_of_lt_of_le Nat.lt_pow_self (Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_max_right _ _))
--   exact Nat.add_eq_xor_impl h₁ h₂ h

-- theorem Nat.add_two_mul_eq_xor {n n' k : Nat} (h : n' < 2 ^ k) : n * 2^k + n' = n * 2^k ^^^ n' := by
--   apply Nat.add_eq_xor
--   intro i
--   by_cases h' : i < k
--   · exact Or.inl (testBit_mul_two_pow_lt h')
--   · exact Or.inr (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_of_not_lt h'))))

-- theorem testBit_mul_two_pow_add_add {n n' k i : Nat} (h : n' < 2 ^ k) :
--     (n * 2^k + n').testBit (i + k) = n.testBit i := by
--   rw [Nat.mul_comm, Nat.testBit_mul_pow_two_add _ h]
--   split
--   · omega
--   · simp

-- instance : Std.Associative (α := Nat) (· + ·) := ⟨Nat.add_assoc⟩
-- instance : Std.Commutative (α := Nat) (· + ·) := ⟨Nat.add_comm⟩
-- instance : Std.Associative (α := Nat) (· * ·) := ⟨Nat.mul_assoc⟩
-- instance : Std.Commutative (α := Nat) (· * ·) := ⟨Nat.mul_comm⟩

-- theorem Nat.exists_lsb {n : Nat} (hn : 0 < n) : ∃ n' k, n = n' * (2^(k+1)) + 2^k := by
--   induction n using Nat.div2Induction
--   next n ih =>
--   skip
--   by_cases h : n % 2 = 0
--   · obtain ⟨n'', k', h'⟩ := ih hn (by omega)
--     refine ⟨n'', k' + 1, ?_⟩
--     rw [← Nat.div_add_mod n 2, h', h, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
--     simp [Nat.mul_add, ← Nat.mul_assoc]
--     ac_rfl -- Why can't omega do this?
--   · have h : n % 2 = 1 := by omega
--     refine ⟨n / 2, 0, ?_⟩
--     simp only [Nat.zero_add, Nat.pow_one, Nat.pow_zero]
--     rw (config := {occs := .pos [1]}) [← Nat.div_add_mod n 2]
--     rw [h, Nat.mul_comm]

-- theorem isPowerOfTwo_iff {n : Nat} : n.isPowerOfTwo ↔ 0 < n ∧ (n &&& (n - 1)) = 0 := by
--   refine ⟨?_, ?_⟩
--   · rintro ⟨k, rfl⟩
--     simpa using Nat.pos_pow_of_pos _ Nat.two_pos
--   · rintro ⟨h₁, h₂⟩
--     obtain ⟨n', k, hn'⟩ := Nat.exists_lsb h₁
--     refine ⟨k, ?_⟩
--     suffices n' = 0 by simp [hn', this]
--     suffices ∀ i, n'.testBit i = false from Nat.eq_of_testBit_eq (by simpa using this)
--     intro i
--     have hn'₁ : n'.testBit i = n.testBit (i + (k + 1)) := by
--       rw [hn', testBit_mul_two_pow_add_add]
--       exact Nat.pow_lt_pow_succ Nat.one_lt_two
--     have hn'₂ : n'.testBit i = (n - 1).testBit (i + (k + 1)) := by
--       rw [hn', Nat.add_sub_assoc (k := 1) (Nat.pow_pos Nat.two_pos), testBit_mul_two_pow_add_add]
--       exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_succ Nat.one_lt_two)
--     calc n'.testBit i = (n'.testBit i && n'.testBit i) := (Bool.and_self _).symm
--       _ = (n.testBit (i + (k + 1)) && (n - 1).testBit (i + (k + 1))) := by simp [← hn'₁, ← hn'₂]
--       _ = ((n &&& (n - 1)).testBit (i + (k + 1))) := by simp
--       _ = ((0 : Nat).testBit (i + (k + 1))) := by rw [h₂]
--       _ = false := by simp

theorem le_of_testBit {n m : Nat} (h : ∀ i, n.testBit i = true → m.testBit i = true) : n ≤ m := by
  induction n using Nat.div2Induction generalizing m
  next n ih =>
  skip
  have : n / 2 ≤ m / 2 := by
    rcases n with (_|n)
    · simp
    · apply ih (Nat.succ_pos _)
      intro i
      simpa using h (i + 1)
  rw [← Nat.div_add_mod n 2, ← Nat.div_add_mod m 2]
  cases hn : n.testBit 0
  · have hn2 : n % 2 = 0 := by simp [Nat.testBit_zero] at hn; omega
    rw [hn2, Nat.add_zero]
    exact Nat.le_trans (Nat.mul_le_mul_left _ this) (Nat.le_add_right _ _)
  · have hn2 : n % 2 = 1 := by simp [Nat.testBit_zero] at hn; omega
    have hm := h _ hn
    have hm2 : m % 2 = 1 := by simp [Nat.testBit_zero] at hm; omega
    rw [hn2, hm2]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _

theorem and_le_left {n m : Nat} : n &&& m ≤ n := by
  apply le_of_testBit
  intro i
  simpa using fun x _ => x

theorem and_le_right {n m : Nat} : n &&& m ≤ m := by
  apply le_of_testBit
  intro i
  simp
