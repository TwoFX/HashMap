/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.HashMap.Basic

set_option autoImplicit false

universe u v

variable {α : Type u}

namespace MyLean

namespace HashSet

structure Raw (α : Type u) where
  inner : HashMap.Raw α Unit

namespace Raw

@[inline] def empty (capacity := 8) : Raw α :=
  ⟨HashMap.Raw.empty capacity⟩

instance : EmptyCollection (Raw α) where
  emptyCollection := empty

@[inline] def insertB [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α × Bool :=
  let ⟨r, replaced⟩ := m.inner.insertB a ()
  ⟨⟨r⟩, replaced⟩

@[inline] def insert [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α :=
  ⟨m.inner.insert a ()⟩

@[inline] def contains [BEq α] [Hashable α] (m : Raw α) (a : α) : Bool :=
  m.inner.contains a

def WF [BEq α] [Hashable α] : Raw α → Prop :=
  fun r => r.inner.WF

theorem WF.empty [BEq α] [Hashable α] {c} : (empty c : Raw α).WF :=
  HashMap.Raw.WF.empty

theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α).WF :=
  HashMap.Raw.WF.empty

theorem WF.insertB [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.insertB a).1.WF :=
  HashMap.Raw.WF.insertB h

theorem WF.insert [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.insert a).WF :=
  HashMap.Raw.WF.insert h

end Raw

end HashSet

structure HashSet (α : Type u) [BEq α] [Hashable α] where
  inner : HashMap α Unit

namespace HashSet

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashSet α :=
  ⟨HashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) where
  emptyCollection := empty

@[inline] def insertB [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α × Bool :=
  let ⟨r, replaced⟩ := m.inner.insertB a ()
  ⟨⟨r⟩, replaced⟩

@[inline] def insert [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.insert a ()⟩

@[inline] def contains [BEq α] [Hashable α] (m : HashSet α) (a : α) : Bool :=
  m.inner.contains a

end HashSet

end MyLean
