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
  raw : DHashMap.Raw α (fun _ => β)

namespace Raw

@[inline] def empty (capacity := 8) : Raw α β :=
  ⟨DHashMap.Raw.empty capacity⟩

@[inline] def insert' [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β × Bool :=
  let ⟨r, replaced⟩ := m.raw.insert' a b
  ⟨⟨r⟩, replaced⟩

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β :=
  ⟨m.raw.insert a b⟩

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option (α × β) :=
  m.raw.findEntry? a |> .map Sigma.toProd

def WF [BEq α] [Hashable α] : Raw α β → Prop :=
  fun r => r.raw.WF

end Raw

end HashMap

def HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] :=
  DHashMap α (fun _ => β)

namespace HashMap

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashMap α β :=
  DHashMap.empty capacity

@[inline] def insert' [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β × Bool :=
  DHashMap.insert' m a b

@[inline] def insert [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  DHashMap.insert m a b

@[inline] def findEntry? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option (α × β) :=
  DHashMap.findEntry? m a |> .map Sigma.toProd

end MyLean.HashMap
