/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Batteries.Data.List.Basic

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w}

namespace List

def keys : List (Σ a, β a) → List α
  | nil => []
  | ⟨k, _⟩ :: l => k :: (keys l)

/-- The well-formedness predicate for `AssocList` says that keys are pairwise distinct. -/
structure DistinctKeys [BEq α] (l : List (Σ a, β a)) : Prop where
  distinct : l.keys.Pairwise fun a b => (a == b) = false

end List
