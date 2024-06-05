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

@[inline] def insertB [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β × Bool :=
  let ⟨r, replaced⟩ := m.inner.insertB a b
  ⟨⟨r⟩, replaced⟩

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β :=
  ⟨m.inner.insert a b⟩

@[inline] def findEntry? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option (α × β) :=
  m.inner.findEntry? a |> .map Sigma.toProd

@[inline] def find? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option β :=
  m.inner.findConst? a

@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  m.inner.contains a

@[inline] def values (m : Raw α β) : List β :=
  m.inner.values

@[inline] def size (m : Raw α β) : Nat :=
  m.inner.size

@[inline] def isEmpty (m : Raw α β) : Bool :=
  m.inner.isEmpty

def WF [BEq α] [Hashable α] : Raw α β → Prop :=
  fun r => r.inner.WF

theorem WF.empty [BEq α] [Hashable α] {c} : (empty c : Raw α β).WF :=
  DHashMap.Raw.WF.empty

theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α β).WF :=
  WF.empty

theorem WF.insertB [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) : (m.insertB a b).1.WF :=
  DHashMap.Raw.WF.insertB h

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) : (m.insert a b).WF :=
  DHashMap.Raw.WF.insert h

end Raw

end HashMap

structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  inner : DHashMap α (fun _ => β)

namespace HashMap

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashMap α β :=
  ⟨DHashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) where
  emptyCollection := empty

@[inline] def insertB [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β × Bool :=
  let ⟨r, replaced⟩ := m.inner.insertB a b
  ⟨⟨r⟩, replaced⟩

@[inline] def insert [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insert a b⟩

@[inline] def findEntry? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option (α × β) :=
  m.inner.findEntry? a |> .map Sigma.toProd

@[inline] def find? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option β :=
  m.inner.findConst? a

@[inline] def contains [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Bool :=
  m.inner.contains a

@[inline] def values [BEq α] [Hashable α] (m : HashMap α β) : List β :=
  m.inner.values

@[inline] def size [BEq α] [Hashable α] (m : HashMap α β) : Nat :=
  m.inner.size

@[inline] def isEmpty [BEq α] [Hashable α] (m : HashMap α β) : Bool :=
  m.inner.isEmpty

end MyLean.HashMap
