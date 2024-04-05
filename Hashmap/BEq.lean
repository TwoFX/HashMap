/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

/-- Class asserting that `BEq` is an equivalence relation. -/
class EquivBEq (α) [BEq α] : Prop where
  /-- Reflexitiivty for `BEq`. -/
  refl : ∀ {a : α}, a == a
  /-- Symmetry for `BEq`. If `a == b` then `b == a`. -/
  symm : ∀ {a b : α}, a == b → b == a
  /-- Transitivity for `BEq`. If `a == b` and `b == c` then `a == c`. -/
  trans : ∀ {a b c : α}, a == b → b == c → a == c

@[simp]
theorem BEq.refl [BEq α] [EquivBEq α] {a : α} : a == a :=
  EquivBEq.refl

theorem BEq.symm [BEq α] [EquivBEq α] {a b : α} : a == b → b == a :=
  EquivBEq.symm

theorem BEq.comm [BEq α] [EquivBEq α] {a b : α} : (a == b) = (b == a) :=
  Bool.eq_iff_iff.2 ⟨BEq.symm, BEq.symm⟩

theorem BEq.symm_false [BEq α] [EquivBEq α] {a b : α} : (a == b) = false → (b == a) = false :=
  BEq.comm (α := α) ▸ id

theorem BEq.trans [BEq α] [EquivBEq α] {a b c : α} : a == b → b == c → a == c :=
  EquivBEq.trans

theorem BEq.neq_of_neq_of_beq [BEq α] [EquivBEq α] {a b c : α} :
    (a == b) = false → b == c → (a == c) = false := by
  refine fun h₁ h₂ => Bool.eq_false_iff.2 fun h₃ => Bool.eq_false_iff.1 h₁ (BEq.trans h₃ (BEq.symm h₂))

theorem BEq.neq_of_beq_of_neq [BEq α] [EquivBEq α] {a b c : α} :
    a == b → (b == c) = false → (a == c) = false := by
  refine fun h₁ h₂ => Bool.eq_false_iff.2 fun h₃ => Bool.eq_false_iff.1 h₂ (BEq.trans (BEq.symm h₁) h₃)

instance (priority := low) [BEq α] [LawfulBEq α] : EquivBEq α where
  refl := LawfulBEq.rfl
  symm h := (beq_iff_eq _ _).2 <| Eq.symm <| (beq_iff_eq _ _).1 h
  trans hab hbc := (beq_iff_eq _ _).2 <| ((beq_iff_eq _ _).1 hab).trans <| (beq_iff_eq _ _).1 hbc
