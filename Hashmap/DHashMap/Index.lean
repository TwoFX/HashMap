/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.PowerOfTwo
import Std.Data.UInt

-- This file needs a lot of clean-up, but I don't really want to get bogged down with this too much at the moment

theorem USize.toNat_and {a b : USize} : (a &&& b).toNat = a.toNat &&& b.toNat := by
  change (a.toNat &&& b.toNat) % _ = _
  rw [Nat.mod_eq_of_lt]
  have : a.toNat < size := a.1.2
  refine Nat.lt_of_le_of_lt and_le_left this

theorem Nat.toNat_toUSize {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a :=
  Nat.mod_eq_of_lt h -- Oooooooooooooooofffffffff

-- Is this not just Fin.coe_sub_iff_le?
theorem USize.toNat_sub_le {a b : Nat} (h : b ≤ a) : a.toUSize - b.toUSize = (a - b).toUSize := by
  apply USize.ext
  change _ % _ = ((a - b) % _)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.mod_add_mod]
  rw [← Nat.add_sub_assoc (Nat.le_of_lt (Nat.mod_lt _ _)), Nat.add_assoc, Nat.add_comm b, Nat.add_sub_assoc, Nat.add_mod]
  · have : (b - b % size) % size = 0 := by
      rw (config := {occs := .pos [1]}) [← Nat.div_add_mod b size]
      rw [Nat.add_sub_cancel]
      simp only [Nat.mul_mod_right]
    rw [this, Nat.add_zero, Nat.mod_mod, Nat.add_mod_right, Nat.add_comm, Nat.add_sub_cancel]
  · exact Nat.mod_le _ _
  · exact Nat.succ_pos _

theorem Nat.toUSize_one : (1 : Nat).toUSize = 1 := rfl

-- An array size is good if it is a small power of two, so that index arithmetic can be performed as bit arithmetic on small numbers.
-- This is also better than just the power-of-two requirement because it ensures that the checkSize method is total.
structure IsGoodSize (sz : Nat) : Prop where
  isPowerOfTwo : sz.isPowerOfTwo
  lt : sz < USize.size

theorem isGoodSize_iff {sz : Nat} : IsGoodSize sz ↔ 0 < sz ∧ sz < USize.size ∧ (sz.toUSize &&& (sz.toUSize - 1)) = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨Nat.pos_of_isPowerOfTwo h₁, h₂, ?_⟩
    rw [isPowerOfTwo_iff] at h₁
    apply USize.ext
    rw [USize.toNat_and, Nat.toNat_toUSize h₂, ← Nat.toUSize_one, USize.toNat_sub_le h₁.1, USize.zero_toNat, Nat.toNat_toUSize]
    · exact h₁.2
    · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h₂
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨?_, h₂⟩
    rw [isPowerOfTwo_iff]
    refine ⟨h₁, ?_⟩
    have := congrArg USize.toNat h₃
    rw [USize.toNat_and, Nat.toNat_toUSize h₂, ← Nat.toUSize_one, USize.toNat_sub_le h₁, USize.zero_toNat, Nat.toNat_toUSize] at this
    · exact this
    · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h₂

@[inline] def checkSize (sz : Nat) : Bool :=
  decide (0 < sz ∧ sz < USize.size ∧ (sz.toUSize &&& (sz.toUSize - 1)) = 0)

theorem checkSize_eq_true {sz : Nat} : checkSize sz = true ↔ IsGoodSize sz := by
  simp [isGoodSize_iff, checkSize]

-- Double the size if it is not already huge
def nextSize (sz : { sz : Nat // IsGoodSize sz }) : { sz : Nat // IsGoodSize sz } :=
  let ⟨n, ⟨h₁, h₂⟩⟩ := sz
  if h : n * 2 < USize.size then
    ⟨n * 2, ⟨Nat.mul2_isPowerOfTwo_of_isPowerOfTwo h₁, h⟩⟩
  else
    ⟨n, ⟨h₁, h₂⟩⟩

-- TODO: benchmark if we need a C implementation for this. Currently this still needs to do a scalar check for sz which we could
-- maybe get rid of, if we changed to size condition in IsGoodSize to assert that sz is definitely a scalar.
def mkIdx {sz : Nat} (hash : UInt64) (h : IsGoodSize sz) : { u : USize // u.toNat < sz } :=
  ⟨hash.toUSize &&& (sz.toUSize - 1), by
    rw [USize.toNat_and, ← Nat.toUSize_one, USize.toNat_sub_le, Nat.toNat_toUSize]
    · obtain ⟨k, rfl⟩ := h.isPowerOfTwo
      simpa using Nat.mod_lt _ (Nat.pow_pos Nat.two_pos)
    · have := h.lt
      omega
    · exact Nat.pos_of_isPowerOfTwo h.isPowerOfTwo⟩

@[simp]
theorem mkIdx_val {sz : Nat} {hash : UInt64} {h : IsGoodSize sz} : (mkIdx hash h).val = hash.toUSize % sz := by
  rw [mkIdx]
  simp
  apply USize.ext
  rw [USize.toNat_and, ← Nat.toUSize_one, USize.toNat_sub_le, Nat.toNat_toUSize]
  · obtain ⟨k, rfl⟩ := h.isPowerOfTwo
    simp
    erw [USize.modn_toNat]
  · have := h.lt
    omega
  · exact Nat.pos_of_isPowerOfTwo h.isPowerOfTwo
