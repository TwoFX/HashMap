/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

@[simp] theorem Option.get!_none [Inhabited α] : (none : Option α).get! = default := rfl
@[simp] theorem Option.get!_some [Inhabited α] {a : α} : (some a).get! = a := rfl
