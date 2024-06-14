/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/

set_option autoImplicit false

universe w v u

namespace MyLean

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w} [Monad m]

/--
`AssocList α β` is "the same as" `List (α × β)`, but flattening the structure
leads to one fewer pointer indirection (in the current code generator).
It is mainly intended as a component of `HashMap`, but it can also be used as a plain
key-value map.
-/
inductive AssocList (α : Type u) (β : α → Type v) where
  /-- An empty list -/
  | nil
  /-- Add a `key, value` pair to the list -/
  | cons (key : α) (value : β key) (tail : AssocList α β)
  deriving Inhabited

namespace AssocList

@[specialize] def foldlM (f : δ → (a : α) → β a → m δ) : (init : δ) → AssocList α β → m δ
  | d, nil         => pure d
  | d, cons a b es => do
    let d ← f d a b
    foldlM f d es

@[inline] def foldl (f : δ → (α : α) → β α → δ) (init : δ) (as : AssocList α β) : δ :=
  Id.run (foldlM f init as)

/--
`O(n)`. Convert an `AssocList α β` into the equivalent `List (α × β)`.
This is used to give specifications for all the `AssocList` functions
in terms of corresponding list functions.
-/
def toList : AssocList α β → List (Σ a, β a)
  | nil => []
  | cons a b es => ⟨a, b⟩ :: es.toList

def length (l : AssocList α β) : Nat :=
  l.foldl (fun n _ _ => n + 1) 0

/-- `O(n)`. Returns the first entry in the list whose key is equal to `a`. -/
def getEntry? [BEq α] (a : α) : AssocList α β → Option (Σ a, β a)
  | nil => none
  | cons k v es => bif k == a then some ⟨k, v⟩ else getEntry? a es

section

variable {β : Type v}

def get? [BEq α] (a : α) : AssocList α (fun _ => β) → Option β
  | nil => none
  | cons k v es => bif k == a then some v else get? a es

end

def getCast? [BEq α] [LawfulBEq α] (a : α) : AssocList α β → Option (β a)
  | nil => none
  | cons k v es => if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else es.getCast? a

@[specialize]
def getWithCast? [BEq α] (a : α) (cast : ∀ {b}, b == a → β b → β a) : AssocList α β → Option (β a)
  | nil => none
  | cons k v es => if h : k == a then some (cast h v) else es.getWithCast? a cast

def getKey? [BEq α] (a : α) : AssocList α β → Option α
  | nil => none
  | cons k _ es => bif k == a then some k else getKey? a es

def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil => false
  | cons k _ l => k == a || l.contains a

def getEntry [BEq α] (a : α) : (l : AssocList α β) → l.contains a → Σ a, β a
  | cons k v es, h => if hka : k == a then ⟨k, v⟩ else getEntry a es
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def get {β : Type v} [BEq α] (a : α) : (l : AssocList α (fun _ => β)) → l.contains a → β
  | cons k v es, h => if hka : k == a then v else get a es
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def getCast [BEq α] [LawfulBEq α] (a : α) : (l : AssocList α β) → l.contains a → β a
  | cons k v es, h => if hka : k == a then cast (congrArg β (eq_of_beq hka)) v else es.getCast a
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

@[specialize]
def getWithCast [BEq α] (a : α) (cast : ∀ {b}, b == a → β b → β a) : (l : AssocList α β) → l.contains a → β a
  | cons k v es, h => if hka : k == a then cast hka v else es.getWithCast a cast
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def replace [BEq α] (a : α) (b : β a) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then cons a b l else cons k v (replace a b l)

def remove [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then l else cons k v (l.remove a)

def insert [BEq α] (l : AssocList α β) (k : α) (v : β k) : AssocList α β :=
  bif l.contains k then l.replace k v else l.cons k v

@[specialize] def alterM [BEq α] [LawfulBEq α] {β : α → Type u} {m : Type u → Type u} [Monad m] (a : α)
    (f : Option (β a) → m (Option (β a))) : AssocList α β → m (AssocList α β)
  | nil => do match ← f none with
    | none => return .nil
    | some v => return .cons a v .nil
  | cons k v t =>
      if h : k == a then do
        match ← f (some (cast (congrArg β (eq_of_beq h)) v)) with
        | none => return t
        | some v' => return .cons a v' t
      else do return .cons k v (← alterM a f t)

@[specialize] def alter [BEq α] [LawfulBEq α] (a : α) (f : Option (β a) → Option (β a)) :
    AssocList α β → AssocList α β
  | nil => match f none with
    | none => .nil
    | some v => .cons a v .nil
  | cons k v t =>
      if h : k == a then
        match f (some (cast (congrArg β (eq_of_beq h)) v)) with
        | none => t
        | some v' => .cons a v' t
      else .cons k v (alter a f t)

@[specialize] def filterMapM [BEq α] {β : α → Type u} {γ : α → Type u} {m : Type u → Type u} [Monad m]
    (f : (a : α) → β a → m (Option (γ a))) : AssocList α β → m (AssocList α γ) :=
  go .nil
where
  @[specialize] go (acc : AssocList α γ) : AssocList α β → m (AssocList α γ)
  | nil => return acc
  | cons k v t => do match ← f k v with
    | none => go acc t
    | some v' => go (cons k v' acc) t

@[specialize] def filterMap (f : (a : α) → β a → Option (γ a)) :
    AssocList α β → AssocList α γ :=
  go .nil
where
  @[specialize] go (acc : AssocList α γ) : AssocList α β → AssocList α γ
  | nil => acc
  | cons k v t => match f k v with
    | none => go acc t
    | some v' => go (cons k v' acc) t

@[specialize] def map (f : (a : α) → β a → γ a) : AssocList α β → AssocList α γ :=
  go .nil
where
  @[specialize] go (acc : AssocList α γ) : AssocList α β → AssocList α γ
  | nil => acc
  | cons k v t => go (cons k (f k v) acc) t

end AssocList

end MyLean
