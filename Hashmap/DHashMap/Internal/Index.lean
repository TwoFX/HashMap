/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.Classes.LawfulHashable
import Hashmap.DHashMap.Internal.List.Associative

open Std.DHashMap.Internal.List

namespace Std.DHashMap.Internal

/--
Scramble the hash code in order to protect against bad hash functions.

Example: if `Hashable Float` was implemented using the "identity" reinterpreting the bit pattern as a `UInt64`,
then the hash codes of all small positive or negative integers would end in around 50 zeroes, meaning that they
all land in bucket 0 in reasonably-sized hash maps.

To counteract this, we xor the hash code with some shifted-down versions of itself, to make sure that all of
the entropy of the hash code appears in the lower 16 bits at least.

The scrambling operation is very fast. It does not have a measurable impact on performance in the insert benchmark.
-/
@[inline]
def scrambleHash (hash : UInt64) : UInt64 :=
  let fold := hash ^^^ (hash >>> 32)
  fold ^^^ (fold >>> 16)

-- Note that this indexing scheme always produces a valid index, but it only has a chance of returning every index if sz is a power of two.
/--
`sz` is an explicit parameter because having it inferred from `h` can lead to suboptimal IR, cf. https://github.com/leanprover/lean4/issues/4157
-/
@[irreducible] def mkIdx (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  ⟨(scrambleHash hash).toUSize &&& (sz.toUSize - 1), by
    -- Making this proof significantly less painful will be a good test for our USize API
    by_cases h' : sz < USize.size
    · rw [USize.toNat_and, ← Nat.toUSize_one, USize.toNat_sub_le, Nat.toNat_toUSize]
      · refine Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt h ?_)
        rw [Nat.toNat_toUSize]
        · exact Nat.one_pos
        · exact Nat.lt_of_le_of_lt h h'
      · exact h'
      · rw [USize.le_def, Fin.le_def]
        change _ ≤ (_ % _)
        rw [Nat.mod_eq_of_lt h', Nat.toUSize, USize.ofNat, Fin.val_ofNat', Nat.mod_eq_of_lt]
        · exact h
        · exact Nat.lt_of_le_of_lt h h'
    · exact Nat.lt_of_lt_of_le USize.toNat_lt' (Nat.le_of_not_lt h')⟩

namespace List

variable {α : Type u} {β : α → Type v}

structure HashesTo [BEq α] [Hashable α] (l : List (Σ a, β a)) (i : Nat) (size : Nat) : Prop where
  hash_self : (h : 0 < size) → ∀ p, p ∈ l → (mkIdx size h (hash p.1)).1.toNat = i

@[simp]
theorem hashesTo_nil [BEq α] [Hashable α] {i : Nat} {size : Nat} :
    HashesTo ([] : List (Σ a, β a)) i size where
  hash_self := by simp

theorem hashesTo_cons [BEq α] [Hashable α] {i : Nat} {size : Nat} {l : List (Σ a, β a)} {k : α}
    {v : β k} (h : (h' : 0 < size) → (mkIdx size h' (hash k)).1.toNat = i) :
    HashesTo l i size → HashesTo (⟨k, v⟩ :: l) i size := by
  refine fun ⟨ih⟩ => ⟨fun h' k' hk => ?_⟩
  simp only [List.mem_cons] at hk
  rcases hk with (rfl|hk)
  · exact h h'
  · exact ih h' _ hk

theorem HashesTo.containsKey_eq_false [BEq α] [Hashable α] [LawfulHashable α] {l : List (Σ a, β a)} {i : Nat} {size : Nat} (hs : 0 < size)
    (h : HashesTo l i size) (k : α) : (mkIdx size hs (hash k)).1.toNat ≠ i → containsKey k l = false := by
  rw [← Decidable.not_imp_not]
  simp only [Bool.not_eq_false, containsKey_eq_true_iff_exists_mem]
  rintro ⟨⟨k', v⟩, hmem, heq⟩
  simp [← h.hash_self hs _ hmem, hash_eq heq]

end List

end Std.DHashMap.Internal
