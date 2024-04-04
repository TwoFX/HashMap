/-! From Mathlib.Data.Option.Basic -/

@[simp] theorem Option.isSome_map (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by
  cases o <;> simp

/-! From Std.Data.List.Lemmas -/

@[simp] theorem List.contains_cons [BEq α] {a : α} {l : List α} {x : α} :
    (a :: l).contains x = (x == a || l.contains x) := rfl

theorem List.erase_cons [BEq α] (a b : α) (l : List α) :
    (b :: l).erase a = if b == a then l else b :: l.erase a := by
  cases h : b == a
  · simp [List.erase, h]
  · simp [List.erase, h]

/-! From Std.Data.List.Basic -/

section

variable (R : α → α → Prop)

inductive List.Pairwise : List α → Prop
  | nil : Pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, R a a') → Pairwise l → Pairwise (a :: l)

attribute [simp] List.Pairwise.nil

end

@[simp] theorem List.pairwise_cons : Pairwise R (a::l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l :=
  ⟨fun | .cons h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩

/-! New results -/

theorem List.contains_iff_exists_beq [BEq α] (l : List α) (a : α) : l.contains a ↔ ∃ a' ∈ l, a == a' := by
  induction l <;> simp_all
