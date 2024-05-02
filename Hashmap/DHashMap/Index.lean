/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.PowerOfTwo
import Std.Data.UInt
import Hashmap.LawfulHashable

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

theorem USize.toNat_lt' {a : USize} : a.toNat < USize.size :=
  a.1.2

-- structure IsGoodSize (sz : Nat) : Prop where
--   pos : 0 < sz
--   lt : sz < USize.size

-- theorem isGoodSize_iff {sz : Nat} : IsGoodSize sz ↔ 0 < sz ∧ sz < USize.size ∧ (sz.toUSize &&& (sz.toUSize - 1)) = 0 := by
--   refine ⟨?_, ?_⟩
--   · rintro ⟨h₁, h₂⟩
--     refine ⟨Nat.pos_of_isPowerOfTwo h₁, h₂, ?_⟩
--     rw [isPowerOfTwo_iff] at h₁
--     apply USize.ext
--     rw [USize.toNat_and, Nat.toNat_toUSize h₂, ← Nat.toUSize_one, USize.toNat_sub_le h₁.1, USize.zero_toNat, Nat.toNat_toUSize]
--     · exact h₁.2
--     · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h₂
--   · rintro ⟨h₁, h₂, h₃⟩
--     refine ⟨?_, h₂⟩
--     rw [isPowerOfTwo_iff]
--     refine ⟨h₁, ?_⟩
--     have := congrArg USize.toNat h₃
--     rw [USize.toNat_and, Nat.toNat_toUSize h₂, ← Nat.toUSize_one, USize.toNat_sub_le h₁, USize.zero_toNat, Nat.toNat_toUSize] at this
--     · exact this
--     · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h₂

-- @[inline] def checkSize (sz : Nat) : Bool :=
--   decide (0 < sz ∧ sz < USize.size)

-- theorem checkSize_eq_true {sz : Nat} : checkSize sz = true ↔ IsGoodSize sz := by
--   simp [checkSize]; exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

-- Double the size if it is not already huge
-- def nextSize (sz : { sz : Nat // IsGoodSize sz }) : { sz : Nat // IsGoodSize sz } :=
--   let ⟨n, ⟨h₁, h₂⟩⟩ := sz
--   if h : n * 2 < USize.size then
--     ⟨n * 2, ⟨Nat.mul_pos h₁ Nat.two_pos, h⟩⟩
--   else
--     ⟨n, ⟨h₁, h₂⟩⟩

-- TODO: benchmark if we need a C implementation for this. Currently this still needs to do a scalar check for sz which we could
-- maybe get rid of, if we changed to size condition in IsGoodSize to assert that sz is definitely a scalar.
-- Note that this indexing scheme always produces a valid index, but it has a chance of returning every index if sz is a power of two.
def mkIdx {sz : Nat} (hash : UInt64) (h : 0 < sz) : { u : USize // u.toNat < sz } :=
  ⟨hash.toUSize &&& (sz.toUSize - 1), by
    by_cases h' : sz < USize.size
    · rw [USize.toNat_and, ← Nat.toUSize_one, USize.toNat_sub_le, Nat.toNat_toUSize]
      · refine Nat.lt_of_le_of_lt and_le_right ?_
        exact Nat.sub_lt h Nat.one_pos
      · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h'
      · exact h
    · exact Nat.lt_of_lt_of_le USize.toNat_lt' (Nat.le_of_not_lt h')⟩

-- @[simp]
-- theorem mkIdx_val {sz : Nat} {hash : UInt64} {h : IsGoodSize sz} : (mkIdx hash h).val = hash.toUSize % sz := by
--   rw [mkIdx]
--   simp
--   apply USize.ext
--   rw [USize.toNat_and, ← Nat.toUSize_one, USize.toNat_sub_le, Nat.toNat_toUSize]
--   · obtain ⟨k, rfl⟩ := h.isPowerOfTwo
--     simp
--     erw [USize.modn_toNat]
--   · have := h.lt
--     omega
--   · exact Nat.pos_of_isPowerOfTwo h.isPowerOfTwo

namespace List

variable {α : Type u} {β : α → Type v}

structure HashesTo [BEq α] [Hashable α] (l : List (Σ a, β a)) (i : Nat) (size : Nat) : Prop where
  hash_self : (h : 0 < size) → ∀ p, p ∈ l → (mkIdx (hash p.1) h).1.toNat = i

@[simp]
theorem hashesTo_nil [BEq α] [Hashable α] {i : Nat} {size : Nat} :
    ([] : List (Σ a, β a)).HashesTo i size where
  hash_self := by simp

theorem hashesTo_cons [BEq α] [Hashable α] [LawfulHashable α] {i : Nat} {size : Nat} {l : List (Σ a, β a)} {k : α}
    {v : β k} (h : (h' : 0 < size) → (mkIdx (hash k) h').1.toNat = i) :
    l.HashesTo i size → (⟨k, v⟩ :: l).HashesTo i size := by
  refine fun ⟨ih⟩ => ⟨fun h' k' hk => ?_⟩
  simp only [mem_cons] at hk
  rcases hk with (rfl|hk)
  · exact h h'
  · exact ih h' _ hk

end List
