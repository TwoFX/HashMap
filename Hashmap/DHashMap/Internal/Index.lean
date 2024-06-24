/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.PowerOfTwo
import Hashmap.LawfulHashable

-- This file needs a lot of clean-up, but I don't really want to get bogged down with this too much at the moment

theorem USize.toNat_and {a b : USize} : (a &&& b).toNat = a.toNat &&& b.toNat := by
  change (a.toNat &&& b.toNat) % _ = _
  rw [Nat.mod_eq_of_lt]
  have : a.toNat < size := a.1.2
  refine Nat.lt_of_le_of_lt and_le_left this

theorem Nat.toNat_toUSize {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a :=
  Nat.mod_eq_of_lt h -- Oooooooooooooooofffffffff

theorem USize.ext : {a b : USize} → a.toNat = b.toNat → a = b
| ⟨⟨_, _⟩⟩, ⟨⟨_, _⟩⟩, rfl => rfl

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

-- set_option trace.compiler.ir.result true in
-- TODO: benchmark if we need a C implementation for this. Currently this still needs to do a scalar check for sz which we could
-- maybe get rid of, if we changed to size condition in IsGoodSize to assert that sz is definitely a scalar.

-- Note that this indexing scheme always produces a valid index, but it only has a chance of returning every index if sz is a power of two.
/--
`sz` is an explicit parameter because having it inferred from `h` can lead to suboptimal IR.
Consider this implementation of `erase`:

```
def erase [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hb⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hb (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    ⟨⟨size - 1, buckets.uset i (bkt.erase a) h⟩, by simpa [-List.length_pos]⟩
  else
    ⟨⟨size, buckets⟩, hb⟩
```

If we do not explicitly provide `buckets.size` to `mkIdx`, then we actually infer
`⟨size, buckets⟩.2.size` for the size argument, so the code generator thinks that we need
the pair `⟨size, buckets⟩` regardless of which branch we take (because it appears as an
argument to `mkIdx`) and it generates this IR:

```
[reset_reuse]
def MyLean.DHashMap.Raw₀.erase._rarg (x_1 : obj) (x_2 : obj) (x_3 : obj) (x_4 : obj) : obj :=
  case x_3 : obj of
  MyLean.DHashMap.Raw.mk →
    let x_5 : obj := proj[0] x_3;
    let x_6 : obj := proj[1] x_3;
    let x_18 : obj := reset[2] x_3;
    let x_7 : obj := reuse x_18 in ctor_0[MyLean.DHashMap.Raw.mk] x_5 x_6;
    let x_8 : obj := Array.size ◾ x_6;
    let x_9 : u64 := app x_2 x_4;
    let x_10 : usize := mkIdx x_8 ◾ x_9;
    let x_11 : obj := Array.uget ◾ x_6 x_10 ◾;
    let x_12 : u8 := MyLean.AssocList.contains._rarg x_1 x_4 x_11;
    case x_12 : obj of
    Bool.false →
      ret x_7
    Bool.true →
      let x_13 : obj := 1;
      let x_14 : obj := Nat.sub x_5 x_13;
      let x_15 : obj := MyLean.AssocList.erase._rarg x_1 x_4 x_11;
      let x_16 : obj := Array.uset ◾ x_6 x_10 x_15 ◾;
      let x_17 : obj := ctor_0[MyLean.DHashMap.Raw.mk] x_14 x_16;
      ret x_17
```

This is suboptimal, because it misses the opportunity to reuse the memory cell of the `Raw`
in case we actually need to erase something. If we provide the argument `buckets.size`, then we
get the better IR

```
[reset_reuse]
def MyLean.DHashMap.Raw₀.erase._rarg (x_1 : obj) (x_2 : obj) (x_3 : obj) (x_4 : obj) : obj :=
  case x_3 : obj of
  MyLean.DHashMap.Raw.mk →
    let x_5 : obj := proj[0] x_3;
    let x_6 : obj := proj[1] x_3;
    let x_18 : obj := reset[2] x_3;
    let x_7 : obj := Array.size ◾ x_6;
    let x_8 : u64 := app x_2 x_4;
    let x_9 : usize := mkIdx x_7 ◾ x_8;
    let x_10 : obj := Array.uget ◾ x_6 x_9 ◾;
    let x_11 : u8 := MyLean.AssocList.contains._rarg x_1 x_4 x_10;
    case x_11 : obj of
    Bool.false →
      let x_12 : obj := reuse x_18 in ctor_0[MyLean.DHashMap.Raw.mk] x_5 x_6;
      ret x_12
    Bool.true →
      let x_13 : obj := 1;
      let x_14 : obj := Nat.sub x_5 x_13;
      let x_15 : obj := MyLean.AssocList.erase._rarg x_1 x_4 x_10;
      let x_16 : obj := Array.uset ◾ x_6 x_9 x_15 ◾;
      let x_17 : obj := reuse x_18 in ctor_0[MyLean.DHashMap.Raw.mk] x_14 x_16;
      ret x_17
```
-/
@[irreducible] def mkIdx (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  ⟨(scrambleHash hash).toUSize &&& (sz.toUSize - 1), by
    by_cases h' : sz < USize.size
    · rw [USize.toNat_and, ← Nat.toUSize_one, USize.toNat_sub_le, Nat.toNat_toUSize]
      · refine Nat.lt_of_le_of_lt and_le_right ?_
        exact Nat.sub_lt h Nat.one_pos
      · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h'
      · exact h
    · exact Nat.lt_of_lt_of_le USize.toNat_lt' (Nat.le_of_not_lt h')⟩

namespace List

variable {α : Type u} {β : α → Type v}

structure HashesTo [BEq α] [Hashable α] (l : List (Σ a, β a)) (i : Nat) (size : Nat) : Prop where
  hash_self : (h : 0 < size) → ∀ p, p ∈ l → (mkIdx size h (hash p.1)).1.toNat = i

@[simp]
theorem hashesTo_nil [BEq α] [Hashable α] {i : Nat} {size : Nat} :
    ([] : List (Σ a, β a)).HashesTo i size where
  hash_self := by simp

theorem hashesTo_cons [BEq α] [Hashable α] [LawfulHashable α] {i : Nat} {size : Nat} {l : List (Σ a, β a)} {k : α}
    {v : β k} (h : (h' : 0 < size) → (mkIdx size h' (hash k)).1.toNat = i) :
    l.HashesTo i size → (⟨k, v⟩ :: l).HashesTo i size := by
  refine fun ⟨ih⟩ => ⟨fun h' k' hk => ?_⟩
  simp only [mem_cons] at hk
  rcases hk with (rfl|hk)
  · exact h h'
  · exact ih h' _ hk

end List
