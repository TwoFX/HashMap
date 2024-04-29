def Option.or : Option α → Option α → Option α
  | o@(some _), _ => o
  | none, o => o

@[simp] theorem Option.or_some {a : α} {o : Option α} : Option.or (some a) o = some a := rfl
@[simp] theorem Option.none_or (o : Option α) : Option.or none o = o := rfl

theorem Option.or_eq_bif {o o' : Option α} : Option.or o o' = bif o.isSome then o else o' := by
  cases o <;> rfl

@[simp]
theorem Option.isSome_or {o o' : Option α} : (Option.or o o').isSome = (o.isSome || o'.isSome) := by
  cases o <;> rfl

@[simp]
theorem Option.isNone_or {o o' : Option α} : (Option.or o o').isNone = (o.isNone && o'.isNone) := by
  cases o <;> rfl

@[simp]
theorem Option.or_eq_none {o o' : Option α} : Option.or o o' = none ↔ o = none ∧ o' = none := by
  cases o <;> simp

theorem Option.or_eq_some {o o' : Option α} {a : α} :
    Option.or o o' = some a ↔ o = some a ∨ (o = none ∧ o' = some a) := by
  cases o <;> simp

theorem Option.or_assoc (o₁ o₂ o₃ : Option α) :
    Option.or (Option.or o₁ o₂) o₃ = Option.or o₁ (Option.or o₂ o₃) := by
  cases o₁ <;> cases o₂ <;> rfl
instance : Std.Associative (Option.or (α := α)) := ⟨Option.or_assoc⟩

@[simp]
theorem Option.or_none (o : Option α) : Option.or o none = o := by
  cases o <;> rfl
instance : Std.LawfulIdentity (Option.or (α := α)) none where
  left_id := Option.none_or
  right_id := Option.or_none

@[simp]
theorem Option.or_self (o : Option α) : Option.or o o = o := by
  cases o <;> rfl
instance : Std.IdempotentOp (Option.or (α := α)) := ⟨Option.or_self⟩

theorem Option.or_eq_orElse (o o' : Option α) : Option.or o o' = o.orElse (fun _ => o') := by
  cases o <;> rfl
