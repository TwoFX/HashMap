/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

namespace List

-- TODO
@[simp] theorem nil_beq_cons [BEq α] {a : α} {as : List α} : ([] == a::as) = false := rfl
@[simp] theorem nil_beq_nil [BEq α] : ([] : List α) == [] := rfl
@[simp] theorem cons_beq_nil [BEq α] {a : α} {as : List α} : (a::as == []) = false := rfl
@[simp] theorem cons_beq_cons [BEq α] {a b : α} {as bs : List α} : (a::as == b::bs) = ((a == b) && as == bs) := rfl

end List
