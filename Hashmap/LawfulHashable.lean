/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

class LawfulHashable (α : Type u) [BEq α] [Hashable α] where
  hash_eq_of_beq (a b : α) : a == b → hash a = hash b
