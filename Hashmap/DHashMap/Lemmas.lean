/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic

set_option autoImplicit false

universe u v

variable {α : Type v} {β : α → Type v}

open List

-- TODO
theorem List.perm_append_comm_assoc (l₁ l₂ l₃ : List α) : l₁ ++ (l₂ ++ l₃) ~ l₂ ++ (l₁ ++ l₃) := by
  simpa only [List.append_assoc] using perm_append_comm.append_right _

namespace MyLean.DHashMap

namespace Raw

end Raw

end MyLean.DHashMap
