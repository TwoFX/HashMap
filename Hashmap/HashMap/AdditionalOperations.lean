/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.AdditionalOperations
import Hashmap.HashMap.Basic

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace MyLean

namespace HashMap

namespace Raw

theorem WF.filterMap [BEq α] [Hashable α] {m : Raw α β} {f : α → β → Option γ} (h : m.WF) : (m.filterMap f).WF :=
  DHashMap.Raw.WF.filterMap h

theorem WF.map [BEq α] [Hashable α] {m : Raw α β} {f : α → β → γ} (h : m.WF) : (m.map f).WF :=
  DHashMap.Raw.WF.map h

end Raw

@[specialize, inline] def filterMap [BEq α] [Hashable α] (f : α → β → Option γ) (m : HashMap α β) : HashMap α γ :=
  ⟨m.inner.filterMap f⟩

@[specialize, inline] def map [BEq α] [Hashable α] (f : α → β → γ) (m : HashMap α β) : HashMap α γ :=
  ⟨m.inner.map f⟩

end HashMap

end MyLean
