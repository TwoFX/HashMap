import Hashmap.HashMap.Lemmas

open MyLean

set_option autoImplicit false

universe u

variable {α : Type u} [BEq α] [Hashable α] [LawfulHashable α]


inductive Inv1 : Nat → HashMap α Nat → Prop where
| empty : Inv1 0 {}
| insert {n : Nat} {map : HashMap α Nat} {x : α}
    (hinv : Inv1 n map) (hfind : map.find? x = none) : Inv1 (n + 1) (map.insert x n)

theorem Inv1.property₂ [EquivBEq α] {n m : Nat} (map : HashMap α Nat) (x : α) (hinv : Inv1 n map) :
    map.find? x = some m → m < n := by
  induction hinv
  · simp
  · next k m' y ih₁ ih₂ ih₃ =>
    skip
    rw [HashMap.find?_insert]
    cases y == x
    · rw [cond_false]
      intro h
      exact Nat.lt_trans (ih₃ h) (Nat.lt_succ_self _)
    · rw [cond_true]
      rintro ⟨rfl⟩
      exact Nat.lt_succ_self _

theorem Inv1.property' [EquivBEq α] {n m : Nat} (x y : α) (map : HashMap α Nat) (hinv : Inv1 n map)
    (hfound1 : map.find? x = some m) (hfound2 : map.find? y = some m) : x == y := by
  induction hinv
  · simp at hfound1
  · next k m' x' ih₁ _ ih₃ =>
    skip
    rw [HashMap.find?_insert] at hfound1
    rw [HashMap.find?_insert] at hfound2
    cases hx : x' == x
    · rw [hx, cond_false] at hfound1
      cases hy : x' == y
      · rw [hy, cond_false] at hfound2
        exact ih₃ hfound1 hfound2
      · rw [hy, cond_true] at hfound2
        rcases hfound2 with ⟨rfl⟩
        have := Inv1.property₂ _ _ ih₁ hfound1
        omega
    · rw [hx, cond_true] at hfound1
      rcases hfound1 with ⟨rfl⟩
      cases hy : x' == y
      · rw [hy, cond_false] at hfound2
        have := Inv1.property₂ _ _ ih₁ hfound2
        omega
      · exact (BEq.trans (BEq.symm hx) hy)

theorem Inv1.property [LawfulBEq α] {n m : Nat} (x y : α) (map : HashMap α Nat) (hinv : Inv1 n map)
    (hfound1 : map.find? x = some m) (hfound2 : map.find? y = some m) : x = y :=
  eq_of_beq (Inv1.property' x y map hinv hfound1 hfound2)
