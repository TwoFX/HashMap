/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

@[simp] theorem Option.get!_none [Inhabited α] : (none : Option α).get! = default := rfl
@[simp] theorem Option.get!_some [Inhabited α] {a : α} : (some a).get! = a := rfl

theorem Option.get_eq_get! [Inhabited α] : (o : Option α) → {h : o.isSome} → o.get h = o.get!
  | some _, _ => rfl

theorem Option.get_eq_getD {fallback : α} : (o : Option α) → {h : o.isSome} → o.get h = o.getD fallback
  | some _, _ => rfl

theorem Option.some_get! [Inhabited α] : (o : Option α) → o.isSome → some (o.get!) = o
  | some _, _ => rfl

theorem Option.get!_eq_getD_default [Inhabited α] (o : Option α) : o.get! = o.getD default := rfl
