/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic
import Hashmap.Sigma

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace MyLean

namespace HashMap

structure Raw (α : Type u) (β : Type v) where
  inner : DHashMap.Raw α (fun _ => β)

namespace Raw

@[inline] def empty (capacity := 8) : Raw α β :=
  ⟨DHashMap.Raw.empty capacity⟩

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

@[inline] def insert' [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β × Bool :=
  let ⟨r, replaced⟩ := m.inner.insert' a b
  ⟨⟨r⟩, replaced⟩

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β :=
  ⟨m.inner.insert a b⟩

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option (α × β) :=
  m.inner.findEntry? a |> .map Sigma.toProd

@[inline] def find? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option β :=
  m.inner.find? a

def WF [BEq α] [Hashable α] : Raw α β → Prop :=
  fun r => r.inner.WF

end Raw

end HashMap

structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  inner : DHashMap α (fun _ => β)

namespace HashMap

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashMap α β :=
  ⟨DHashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) where
  emptyCollection := empty

@[inline] def insert' [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β × Bool :=
  let ⟨r, replaced⟩ := m.inner.insert' a b
  ⟨⟨r⟩, replaced⟩

@[inline] def insert [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insert a b⟩

@[inline] def findEntry? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option (α × β) :=
  m.inner.findEntry? a |> .map Sigma.toProd

@[inline] def find? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option β :=
  m.inner.find? a

end MyLean.HashMap
