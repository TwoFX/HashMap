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

@[inline] def insert [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α :=
  ⟨m.inner.insert a ()⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α × Bool :=
  let ⟨r, replaced⟩ := m.inner.containsThenInsert a ()
  ⟨⟨r⟩, replaced⟩

@[inline] def contains [BEq α] [Hashable α] (m : Raw α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (Raw α) where
  mem a m := m.contains a

@[inline] def remove [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α :=
  ⟨m.inner.remove a⟩

@[inline] def filter [BEq α] [Hashable α] (f : α → Bool) (m : Raw α) : Raw α :=
  ⟨m.inner.filter fun a _ => f a⟩

@[inline] def foldlM {m : Type v → Type v} [Monad m] {β : Type v} (f : β → α → m β) (init : β) (b : Raw α) : m β :=
  b.inner.foldlM (fun b a _ => f b a) init

@[inline] def foldl {β : Type v} (f : β → α → β) (init : β) (m : Raw α) : β :=
  m.inner.foldl (fun b a _ => f b a) init

@[inline] def size (m : Raw α) : Nat :=
  m.inner.size

@[inline] def isEmpty (m : Raw α) : Bool :=
  m.inner.isEmpty

def WF [BEq α] [Hashable α] : Raw α → Prop :=
  fun r => r.inner.WF

theorem WF.empty [BEq α] [Hashable α] {c} : (empty c : Raw α).WF :=
  HashMap.Raw.WF.empty

theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α).WF :=
  HashMap.Raw.WF.empty

theorem WF.insert [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.insert a).WF :=
  HashMap.Raw.WF.insert h

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.containsThenInsert a).1.WF :=
  HashMap.Raw.WF.containsThenInsert h

theorem WF.remove [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.remove a).WF :=
  HashMap.Raw.WF.remove h

theorem WF.filter [BEq α] [Hashable α] {m : Raw α} {f : α → Bool} (h : m.WF) : (m.filter f).WF :=
  HashMap.Raw.WF.filter h

end Raw

end HashSet

structure HashSet (α : Type u) [BEq α] [Hashable α] where
  inner : HashMap α Unit

namespace HashSet

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashSet α :=
  ⟨HashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.insert a ()⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α × Bool :=
  let ⟨r, replaced⟩ := m.inner.containsThenInsert a ()
  ⟨⟨r⟩, replaced⟩

@[inline] def contains [BEq α] [Hashable α] (m : HashSet α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashSet α) where
  mem a m := m.contains a

@[inline] def remove [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.remove a⟩

@[inline] def filter [BEq α] [Hashable α] (f : α → Bool) (m : HashSet α) : HashSet α :=
  ⟨m.inner.filter fun a _ => f a⟩

@[inline] def foldlM [BEq α] [Hashable α] {m : Type v → Type v} [Monad m] {β : Type v} (f : β → α → m β) (init : β) (b : HashSet α) : m β :=
  b.inner.foldlM (fun b a _ => f b a) init

@[inline] def foldl [BEq α] [Hashable α] {β : Type v} (f : β → α → β) (init : β) (m : HashSet α) : β :=
  m.inner.foldl (fun b a _ => f b a) init

@[inline] def size [BEq α] [Hashable α] (m : HashSet α) : Nat :=
  m.inner.size

@[inline] def isEmpty [BEq α] [Hashable α] (m : HashSet α) : Bool :=
  m.inner.isEmpty

end HashSet

end MyLean
