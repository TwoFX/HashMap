/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

@[inline] def Sigma.toProd : (_ : α) × β → α × β
  | ⟨a, b⟩ => (a, b)

@[simp]
theorem Sigma.toProd_mk {a : α} {b : β} : (⟨a, b⟩ : (_ : α) × β).toProd = (a, b) := rfl
