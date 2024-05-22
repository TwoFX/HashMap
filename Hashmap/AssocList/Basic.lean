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

@[simp] theorem toList_nil : (nil : AssocList α β).toList = [] := rfl
@[simp] theorem toList_cons {l : AssocList α β} {a : α} {b : β a} : (l.cons a b).toList = ⟨a, b⟩ :: l.toList := rfl

@[simp]
theorem foldl_eq {f : δ → (a : α) → β a → δ} {init : δ} {l : AssocList α β} :
    l.foldl f init = l.toList.foldl (fun d p => f d p.1 p.2) init := by
  induction l generalizing init <;> simp_all [foldl, Id.run, foldlM]

def length (l : AssocList α β) : Nat :=
  l.foldl (fun n _ _ => n + 1) 0

/-- `O(n)`. Returns the first entry in the list whose key is equal to `a`. -/
def findEntry? [BEq α] (a : α) : AssocList α β → Option (Σ a, β a)
  | nil => none
  | cons k v es => bif k == a then some ⟨k, v⟩ else findEntry? a es

section

variable {β : Type v}

def find? [BEq α] (a : α) : AssocList α (fun _ => β) → Option β
  | nil => none
  | cons k v es => bif k == a then some v else find? a es

end

def findCast? [BEq α] [LawfulBEq α] (a : α) : AssocList α β → Option (β a)
  | nil => none
  | cons k v es => if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else es.findCast? a

def findKey? [BEq α] (a : α) : AssocList α β → Option α
  | nil => none
  | cons k _ es => bif k == a then some k else findKey? a es

def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil => false
  | cons k _ l => k == a || l.contains a

def findEntry [BEq α] (a : α) : (l : AssocList α β) → l.contains a → Σ a, β a
  | nil, h => absurd h Bool.false_ne_true
  | cons k v es, h => if hka : k == a then ⟨k, v⟩ else findEntry a es
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def find {β : Type v} [BEq α] (a : α) : (l : AssocList α (fun _ => β)) → l.contains a → β
  | nil, h => absurd h Bool.false_ne_true
  | cons k v es, h => if hka : k == a then v else find a es
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def findCast [BEq α] [LawfulBEq α] (a : α) : (l : AssocList α β) → l.contains a → β a
  | nil, h => absurd h Bool.false_ne_true
  | cons k v es, h => if hka : k == a then cast (congrArg β (eq_of_beq hka)) v else es.findCast a
      (by rw [← h, contains, Bool.of_not_eq_true hka, Bool.false_or])

def replace [BEq α] (a : α) (b : β a) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then cons a b l else cons k v (replace a b l)

def erase [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then l else cons k v (l.erase a)

def insert [BEq α] (l : AssocList α β) (k : α) (v : β k) : AssocList α β :=
  bif l.contains k then l.replace k v else l.cons k v

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
