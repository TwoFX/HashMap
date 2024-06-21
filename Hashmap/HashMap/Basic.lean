/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic
import Hashmap.Sigma

set_option autoImplicit false

universe u v w

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

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β :=
  ⟨m.inner.insert a b⟩

@[inline] def insertIfNew [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β :=
  ⟨m.inner.insertIfNew a b⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β × Bool :=
  let ⟨r, replaced⟩ := m.inner.containsThenInsert a b
  ⟨⟨r⟩, replaced⟩

@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) : Raw α β × Option β :=
  let ⟨r, previous⟩ := DHashMap.Raw.Const.getThenInsertIfNew? m.inner a b
  ⟨⟨r⟩, previous⟩

@[inline] def get? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option β :=
  DHashMap.Raw.Const.get? m.inner a

@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (Raw α β) where
  mem a m := m.contains a

@[inline] def get [BEq α] [Hashable α] (m : Raw α β) (a : α) (h : a ∈ m) : β :=
  DHashMap.Raw.Const.get m.inner a h

@[inline] def getD [BEq α] [Hashable α] (m : Raw α β) (a : α) (fallback : β) : β :=
  DHashMap.Raw.Const.getD m.inner a fallback

@[inline] def get! [BEq α] [Hashable α] [Inhabited β] (m : Raw α β) (a : α) : β :=
  DHashMap.Raw.Const.get! m.inner a

instance [BEq α] [Hashable α] : GetElem (Raw α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline] def remove [BEq α] [Hashable α] (m : Raw α β) (a : α) : Raw α β :=
  ⟨m.inner.remove a⟩

@[inline] def filterMap {γ : Type w} (f : α → β → Option γ) (m : Raw α β) : Raw α γ :=
  ⟨m.inner.filterMap f⟩

@[inline] def map {γ : Type w} (f : α → β → γ) (m : Raw α β) : Raw α γ :=
  ⟨m.inner.map f⟩

@[inline] def filter (f : α → β → Bool) (m : Raw α β) : Raw α β :=
  ⟨m.inner.filter f⟩

@[inline] def foldlM {m : Type w → Type w} [Monad m] {γ : Type w} (f : γ → α → β → m γ) (init : γ) (b : Raw α β) : m γ :=
  b.inner.foldlM f init

@[inline] def foldl {γ : Type w} (f : γ → α → β → γ) (init : γ) (b : Raw α β) : γ :=
  b.inner.foldl f init

@[inline] def toList (m : Raw α β) : List (α × β) :=
  DHashMap.Raw.Const.toList m.inner

@[inline] def toArray (m : Raw α β) : Array (α × β) :=
  DHashMap.Raw.Const.toArray m.inner

@[inline] def keys (m : Raw α β) : List α :=
  m.inner.keys

@[inline] def keysArray (m : Raw α β) : Array α :=
  m.inner.keysArray

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

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) : (m.insert a b).WF :=
  DHashMap.Raw.WF.insert h

theorem WF.insertIfNew [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) : (m.insertIfNew a b).WF :=
  DHashMap.Raw.WF.insertIfNew h

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) : (m.containsThenInsert a b).1.WF :=
  DHashMap.Raw.WF.containsThenInsert h

theorem WF.getThenInsertIfNew? [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) : (m.getThenInsertIfNew? a b).1.WF :=
  DHashMap.Raw.WF.Const.getThenInsertIfNew? h

theorem WF.remove [BEq α] [Hashable α] {m : Raw α β} {a : α} (h : m.WF) : (m.remove a).WF :=
  DHashMap.Raw.WF.remove h

theorem WF.filter [BEq α] [Hashable α] {m : Raw α β} {f : α → β → Bool} (h : m.WF) : (m.filter f).WF :=
  DHashMap.Raw.WF.filter h

end Raw

end HashMap

structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  inner : DHashMap α (fun _ => β)

namespace HashMap

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashMap α β :=
  ⟨DHashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insert a b⟩

@[inline] def insertIfNew [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insertIfNew a b⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β × Bool :=
  let ⟨r, replaced⟩ := m.inner.containsThenInsert a b
  ⟨⟨r⟩, replaced⟩

@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β × Option β :=
  let ⟨r, previous⟩ := DHashMap.Const.getThenInsertIfNew? m.inner a b
  ⟨⟨r⟩, previous⟩

@[inline] def get? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option β :=
  DHashMap.Const.get? m.inner a

@[inline] def contains [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashMap α β) where
  mem a m := m.contains a

@[inline] def get [BEq α] [Hashable α] (m : HashMap α β) (a : α) (h : a ∈ m) : β :=
  DHashMap.Const.get m.inner a h

@[inline] def getD [BEq α] [Hashable α] (m : HashMap α β) (a : α) (fallback : β) : β :=
  DHashMap.Const.getD m.inner a fallback

@[inline] def get! [BEq α] [Hashable α] [Inhabited β] (m : HashMap α β) (a : α) : β :=
  DHashMap.Const.get! m.inner a

instance [BEq α] [Hashable α] : GetElem (HashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline] def remove [BEq α] [Hashable α] (m : HashMap α β) (a : α) : HashMap α β :=
  ⟨m.inner.remove a⟩

@[inline] def filter [BEq α] [Hashable α] (f : α → β → Bool) (m : HashMap α β) : HashMap α β :=
  ⟨m.inner.filter f⟩

@[inline] def foldlM [BEq α] [Hashable α] {m : Type w → Type w} [Monad m] {γ : Type w} (f : γ → α → β → m γ) (init : γ) (b : HashMap α β) : m γ :=
  b.inner.foldlM f init

@[inline] def foldl [BEq α] [Hashable α] {γ : Type w} (f : γ → α → β → γ) (init : γ) (b : HashMap α β) : γ :=
  b.inner.foldl f init

@[inline] def toList (m : Raw α β) : List (α × β) :=
  DHashMap.Raw.Const.toList m.inner

@[inline] def toArray (m : Raw α β) : Array (α × β) :=
  DHashMap.Raw.Const.toArray m.inner

@[inline] def keys [BEq α] [Hashable α] (m : HashMap α β) : List α :=
  m.inner.keys

@[inline] def keysArray [BEq α] [Hashable α] (m : HashMap α β) : Array α :=
  m.inner.keysArray

@[inline] def values [BEq α] [Hashable α] (m : HashMap α β) : List β :=
  m.inner.values

@[inline] def size [BEq α] [Hashable α] (m : HashMap α β) : Nat :=
  m.inner.size

@[inline] def isEmpty [BEq α] [Hashable α] (m : HashMap α β) : Bool :=
  m.inner.isEmpty

end MyLean.HashMap
