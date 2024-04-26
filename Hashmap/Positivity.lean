import Lean.Data.HashMap

set_option autoImplicit false

universe v u

abbrev Buckets (α : Type u) (β : Type v) := Array (Lean.AssocList α β)

inductive SS (α : Type u) (β : Type v) where
  | base
  | coll (l : Buckets Bool (SS α β))

inductive SS' (α : Type u) (β : Type v) where
  | base
  | coll (l : Array (Lean.AssocList Bool (SS' α β)))
  


inductive MyList (α : Type u)
  | nil
  | cons (head : α) (tail : MyList α)

inductive MyNonemptyList (α : Type u)
  | single (head : α)
  | cons (head : α) (tail : MyNonemptyList α)

def MyList.length {α : Type u} : MyList α → Nat
  | MyList.nil => 0
  | MyList.cons _ tail => length tail + 1

structure B (α : Type u) where
  b : MyNonemptyList (MyList α)

inductive S where
  | base
  | coll (l : B S)

def B' (α : Type u) :=
  { _a : MyNonemptyList (MyList α) // true }

inductive S' where
  | base
  | coll (l : B' S')

inductive S'₂ where
  | base
  | coll (l : { _a : MyNonemptyList (MyList S'₂) // true})

def B'' (α : Type u) :=
  { _a : MyList (MyList α) // true }

inductive S'' where
  | base
  | coll (l : B'' S'')

def Buckets (α : Type u) :=
  { b : MyList (MyList α) // 0 < b.length }

inductive T where
  | base
  | other (l : Buckets T)

structure Buckets' (α : Type u) where
  b : List (List α)
  prop : 0 < b.length

inductive U where
  | base
  | other (l : Buckets' U)
