import Std.Data.List.Lemmas
/-! From Mathlib.Data.Option.Basic -/

@[simp] theorem Option.isSome_map (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by
  cases o <;> simp


-- /-! From Std.Data.List.Basic -/

-- section

-- variable (R : α → α → Prop)

-- inductive List.Pairwise : List α → Prop
--   | nil : Pairwise []
--   | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, R a a') → Pairwise l → Pairwise (a :: l)

-- attribute [simp] List.Pairwise.nil

-- end

-- @[simp] theorem List.pairwise_cons : Pairwise R (a::l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l :=
--   ⟨fun | .cons h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩

-- /-- `l₁ <+ l₂`, or `Sublist l₁ l₂`, says that `l₁` is a (non-contiguous) subsequence of `l₂`. -/
-- inductive List.Sublist {α} : List α → List α → Prop
--   /-- the base case: `[]` is a sublist of `[]` -/
--   | slnil : Sublist [] []
--   /-- If `l₁` is a subsequence of `l₂`, then it is also a subsequence of `a :: l₂`. -/
--   | cons a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
--   /-- If `l₁` is a subsequence of `l₂`, then `a :: l₁` is a subsequence of `a :: l₂`. -/
--   | cons₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

-- namespace List

-- @[inherit_doc] scoped infixl:50 " <+ " => Sublist

-- end List


-- /-! From Std.Data.List.Lemmas -/

-- @[simp] theorem List.contains_cons [BEq α] {a : α} {l : List α} {x : α} :
--     (a :: l).contains x = (x == a || l.contains x) := rfl

-- theorem List.erase_cons [BEq α] (a b : α) (l : List α) :
--     (b :: l).erase a = if b == a then l else b :: l.erase a := by
--   cases h : b == a
--   · simp [List.erase, h]
--   · simp [List.erase, h]

-- section

open List

theorem List.erase_sublist' [BEq α] (a : α) (l : List α) : l.erase a <+ l := by
  induction l
  · simp
  · next a' l ih =>
    rw [erase_cons]
    cases a' == a
    · simpa using Sublist.cons₂ _ ih
    · simp

-- theorem List.Pairwise.sublist (R : α → α → Prop) (l₁ l₂ : List α) : l₁ <+ l₂ → l₂.Pairwise R → l₁.Pairwise R := sorry

-- @[simp] theorem List.Sublist.refl : ∀ l : List α, l <+ l := sorry

-- end

-- /-! From Std.Data.Array.Lemmas -/

-- theorem Array.get_set (a : Array α) (i : Fin a.size) (j : Nat) (hj : j < a.size) (v : α) :
--     (a.set i v)[j]'(by simp [*]) = if i = j then v else a[j] := sorry

-- /-! New results -/

theorem List.contains_iff_exists_beq [BEq α] (l : List α) (a : α) : l.contains a ↔ ∃ a' ∈ l, a == a' := by
  induction l <;> simp_all

theorem apply_bif (f : α → β) {b : Bool} {a a' : α} :
    f (bif b then a else a') = bif b then f a else f a' := by
  cases b <;> simp

@[simp]
theorem bif_const {b : Bool} {a : α} : (bif b then a else a) = a := by
  cases b <;> simp
