import Hashmap.DHashMap.Basic

open Std

universe u v w

set_option autoImplicit false

def MemoizeT {α : Type u} [BEq α] [Hashable α] {β : α → Type u}
    (m : Type u → Type v) (_f : (a : α) → m (β a)) (γ : Type u) : Type (max u v) :=
  StateT (DHashMap.Raw α β) m γ

def MemoizeT.run {α : Type u} [BEq α] [Hashable α] {β : α → Type u}
    {m : Type u → Type v} [Functor m] {f : (a : α) → m (β a)} {γ : Type u} (x : MemoizeT m f γ) : m γ :=
  StateT.run' x ∅

@[reducible]
def MemoizeM {α : Type u} [BEq α] [Hashable α] {β : α → Type u} (f : (a : α) → β a) (γ : Type u) :=
  MemoizeT Id f γ

def MemoizeM.run {α : Type u} [BEq α] [Hashable α] {β : α → Type u} {f : (a : α) → β a} {γ : Type u}
    (x : MemoizeM f γ) : γ :=
  MemoizeT.run x

namespace MemoizeT

variable {α : Type u} [BEq α] [Hashable α] {β : α → Type u} {m : Type u → Type v} [Monad m]
  {f : (a : α) → m (β a)} {γ δ : Type u}

@[always_inline, inline]
protected def pure (a : γ) : MemoizeT m f γ :=
  StateT.pure a

@[always_inline, inline]
protected def bind (x : MemoizeT m f γ) (g : γ → MemoizeT m f δ) : MemoizeT m f δ :=
  StateT.bind x g

@[always_inline, inline]
protected def map (g : γ → δ) (x : MemoizeT m f γ) : MemoizeT m f δ :=
  StateT.map g x

instance : Monad (MemoizeT m f) where
  pure := MemoizeT.pure
  bind := MemoizeT.bind
  map := MemoizeT.map

@[always_inline, inline]
protected def lift (t : m γ) : MemoizeT m f γ :=
  StateT.lift t

protected def calculate [LawfulBEq α] (a : α) : MemoizeT m f (β a) :=
  show StateT (DHashMap.Raw α β) m (β a) from do -- correct way would be to provide the MonadState instance for MemoizeT
  let (newCache, result) ← (← get).computeIfAbsentM a (fun _ => MemoizeT.lift (f := f) (f a))
  set newCache
  return result

end MemoizeT
