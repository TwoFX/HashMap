/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.List.Associative

set_option autoImplicit false

universe w v u

namespace MyLean

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

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
theorem foldl_eq [BEq α] {f : δ → (a : α) → β a → δ} {init : δ} {l : AssocList α β} :
    l.foldl f init = l.toList.foldl (fun d p => f d p.1 p.2) init := by
  induction l generalizing init <;> simp_all [foldl, Id.run, foldlM]

/-- `O(n)`. Returns the first entry in the list whose key is equal to `a`. -/
def findEntry? [BEq α] (a : α) : AssocList α β → Option (Σ a, β a)
  | nil => none
  | cons k v es => bif k == a then some ⟨k, v⟩ else findEntry? a es

@[simp]
theorem findEntry?_eq [BEq α] {l : AssocList α β} {a : α} : l.findEntry? a = l.toList.findEntry? a := by
  induction l <;> simp_all [findEntry?, List.findEntry?]

section

variable {β : Type v}

def find? [BEq α] (a : α) : AssocList α (fun _ => β) → Option β
  | nil => none
  | cons k v es => bif k == a then some v else find? a es

@[simp]
theorem find?_eq [BEq α] {l : AssocList α (fun _ => β)} {a : α} : l.find? a = l.toList.findValue? a := by
  induction l <;> simp_all [find?, List.findValue?]

end

def findKey? [BEq α] (a : α) : AssocList α β → Option α
  | nil => none
  | cons k _ es => bif k == a then some k else findKey? a es

@[simp]
theorem findKey?_eq [BEq α] {l : AssocList α β} {a : α} : l.findKey? a = l.toList.findKey? a := by
  induction l <;> simp_all [findKey?, List.findKey?]

def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil => false
  | cons k _ l => k == a || l.contains a

@[simp]
theorem contains_eq [BEq α] {l : AssocList α β} {a : α} : l.contains a = l.toList.containsKey a := by
  induction l <;> simp_all [contains, List.containsKey]

-- def findEntry [BEq α] (l : AssocList α β) (a : α) (h : l.contains a) : Σ a, β a :=
--   (l.findEntry? a).get <| contains_eq_isSome_findEntry?.symm.trans h

-- def findKey [BEq α] (l : AssocList α β) (a : α) (h : l.contains a) : α :=
--   (l.findKey? a).get <| contains_eq_isSome_findKey?.symm.trans h

-- section

-- variable {β : Type v}

-- def find [BEq α] (l : AssocList' α β) (a : α) (h : l.contains a) : β :=
--   (l.find? a).get <| contains_eq_isSome_find?.symm.trans h

-- end

def replace [BEq α] (a : α) (b : β a) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then cons a b l else cons k v (replace a b l)

@[simp]
theorem toList_replace [BEq α] {l : AssocList α β} {a : α} {b : β a} :
    (l.replace a b).toList = l.toList.replaceEntry a b := by
  induction l
  · simp [replace]
  · next k v t ih => cases h : k == a <;> simp_all [replace, List.replaceEntry_cons]

def erase [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then l else cons k v (l.erase a)

@[simp]
theorem toList_erase [BEq α] {l : AssocList α β} {a : α} : (l.erase a).toList = l.toList.eraseKey a := by
  induction l
  · simp [erase]
  · next k v t ih => cases h : k == a <;> simp_all [erase, List.eraseKey_cons]

def insert [BEq α] (l : AssocList α β) (k : α) (v : β k) : AssocList α β :=
  bif l.contains k then l.replace k v else l.cons k v

@[simp]
theorem toList_insert [BEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.insert k v).toList = l.toList.insertEntry k v := by
  simp [insert, List.insertEntry, apply_bif toList]

end AssocList

end MyLean
