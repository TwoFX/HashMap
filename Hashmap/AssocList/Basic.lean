/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.ForUpstream
import Hashmap.BEq

namespace Lean

/--
`AssocList α β` is "the same as" `List (α × β)`, but flattening the structure
leads to one fewer pointer indirection (in the current code generator).
It is mainly intended as a component of `HashMap`, but it can also be used as a plain
key-value map.
-/
inductive AssocList (α : Type u) (β : Type v) where
  /-- An empty list -/
  | nil
  /-- Add a `key, value` pair to the list -/
  | cons (key : α) (value : β) (tail : AssocList α β)
  deriving Inhabited

namespace AssocList

/--
`O(n)`. Convert an `AssocList α β` into the equivalent `List (α × β)`.
This is used to give specifications for all the `AssocList` functions
in terms of corresponding list functions.
-/
def toList : AssocList α β → List (α × β)
  | nil => []
  | cons a b es => (a, b) :: es.toList

@[simp] theorem toList_nil : (nil : AssocList α β).toList = [] := rfl
@[simp] theorem toList_cons {l : AssocList α β} {a : α} {b : β} : (l.cons a b).toList = (a, b) :: l.toList := rfl

/-- `O(n)`. Returns the first entry in the list whose key is equal to `a`. -/
def findEntry? [BEq α] (a : α) : AssocList α β → Option (α × β)
  | nil => none
  | cons k v es => bif k == a then some (k, v) else findEntry? a es

@[simp] theorem findEntry?_nil [BEq α] {a : α} : (nil : AssocList α β).findEntry? a = none := rfl

theorem findEntry?_cons_of_true [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).findEntry? a = some (k, v) := by
  simp [findEntry?, h]

theorem findEntry?_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : (k == a) = false) :
    (l.cons k v).findEntry? a = l.findEntry? a := by
  simp [findEntry?, h]

theorem findEntry?_cons [BEq α] {l : AssocList α β} {k a : α} {v : β} :
    (l.cons k v).findEntry? a = bif k == a then some (k, v) else l.findEntry? a := rfl

def find? [BEq α] (a : α) : AssocList α β → Option β
  | nil => none
  | cons k v es => bif k == a then some v else find? a es

@[simp] theorem find?_nil [BEq α] {a : α} : (nil : AssocList α β).find? a = none := rfl

theorem find?_cons_of_true [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).find? a = some v := by
  simp [find?, h]

theorem find?_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : (k == a) = false) :
    (l.cons k v).find? a = l.find? a := by
  simp [find?, h]

theorem find?_eq_findEntry? [BEq α] (a : α) (l : AssocList α β) :
    find? a l = (l.findEntry? a).map (·.2) := by
  induction l
  · simp
  · next k v es ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, find?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, find?_cons_of_true h, Option.map_some']

def findKey? [BEq α] (a : α) : AssocList α β → Option α
  | nil => none
  | cons k _ es => bif k == a then some k else findKey? a es

@[simp] theorem findKey?_nil [BEq α] {a : α} : (nil : AssocList α β).findKey? a = none := rfl

theorem findKey?_cons_of_true [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).findKey? a = some k := by
  simp [findKey?, h]

theorem findKey?_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : (k == a) = false) :
    (l.cons k v).findKey? a = l.findKey? a := by
  simp [findKey?, h]

theorem findKey?_eq_findEntry? [BEq α] (a : α) (l : AssocList α β) :
    findKey? a l = (l.findEntry? a).map (·.1) := by
  induction l
  · simp
  · next k v es ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, findKey?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, findKey?_cons_of_true h, Option.map_some']

def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil => false
  | cons k _ l => k == a || l.contains a

@[simp] theorem contains_nil [BEq α] : (nil : AssocList α β).contains a = false := rfl
@[simp] theorem contains_cons [BEq α] {l : AssocList α β} {k a : α} {v : β} :
    (l.cons k v).contains a = (k == a || l.contains a) := rfl

theorem contains_cons_eq_false [BEq α] {l : AssocList α β} {k a : α} {v : β} :
    ((l.cons k v).contains a = false) ↔ ((k == a) = false) ∧ (l.contains a = false) := by
  rw [Bool.eq_iff_iff]
  simp [contains_cons, not_or]

theorem contains_cons_eq_true [BEq α] {l : AssocList α β} {k a : α} {v : β} :
    ((l.cons k v).contains a) ↔ (k == a) ∨ (l.contains a) := by
  rw [Bool.eq_iff_iff]
  simp [contains_cons]

theorem contains_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).contains a := contains_cons_eq_true.2 <| Or.inl h

theorem contains_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.cons k v).contains k := contains_cons_of_beq BEq.refl

theorem contains_cons_of_contains [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : l.contains a) :
    (l.cons k v).contains a := contains_cons_eq_true.2 <| Or.inr h

theorem contains_of_contains_cons [BEq α] {l : AssocList α β} {k a : α} {v : β} (h₁ : (l.cons k v).contains a)
    (h₂ : (k == a) = false) : l.contains a := by
  rcases (contains_cons_eq_true.1 h₁) with (h|h)
  · exact False.elim (Bool.eq_false_iff.1 h₂ h)
  · exact h

theorem contains_eq_isSome_findEntry? [BEq α] (l : AssocList α β) {a : α} :
    l.contains a = (l.findEntry? a).isSome := by
  induction l
  · simp
  · next k v l ih =>
    cases h : k == a
    · simp [findEntry?_cons_of_false h, h, ih]
    · simp [findEntry?_cons_of_true h, h]

theorem contains_eq_isSome_find? [BEq α] (l : AssocList α β) {a : α} :
    l.contains a = (l.find? a).isSome := by
  simp [contains_eq_isSome_findEntry?, find?_eq_findEntry?]

theorem contains_eq_isSome_findKey? [BEq α] (l : AssocList α β) {a : α} :
    l.contains a = (l.findKey? a).isSome := by
  simp [contains_eq_isSome_findEntry?, findKey?_eq_findEntry?]

def findEntry [BEq α] (l : AssocList α β) (a : α) (h : l.contains a) : α × β :=
  (l.findEntry? a).get <| (contains_eq_isSome_findEntry? l).symm.trans h

theorem findEntry?_eq_some_findEntry [BEq α] {l : AssocList α β} {a : α} (h : l.contains a) :
    l.findEntry? a = some (l.findEntry a h) := by
  simp [findEntry]

theorem findEntry_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).findEntry a (contains_cons_of_beq h) = (k, v) := by
  simp [findEntry, findEntry?_cons_of_true h]

@[simp]
theorem findEntry_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.cons k v).findEntry k contains_cons_self = (k, v) :=
  findEntry_cons_of_beq BEq.refl

theorem findEntry_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β} {h₁ : (l.cons k v).contains a}
    (h₂ : (k == a) = false) : (l.cons k v).findEntry a h₁ = l.findEntry a (contains_of_contains_cons h₁ h₂) := by
  simp [findEntry, findEntry?_cons_of_false h₂]

def findKey [BEq α] (l : AssocList α β) (a : α) (h : l.contains a) : α :=
  (l.findKey? a).get <| (contains_eq_isSome_findKey? l).symm.trans h

theorem findKey?_eq_some_findKey [BEq α] {l : AssocList α β} {a : α} (h : l.contains a) :
    l.findKey? a = some (l.findKey a h) := by
  simp [findKey]

theorem findKey_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).findKey a (contains_cons_of_beq h) = k := by
  simp [findKey, findKey?_cons_of_true h]

@[simp]
theorem findKey_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.cons k v).findKey k contains_cons_self = k :=
  findKey_cons_of_beq BEq.refl

theorem findKey_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β} {h₁ : (l.cons k v).contains a}
    (h₂ : (k == a) = false) : (l.cons k v).findKey a h₁ = l.findKey a (contains_of_contains_cons h₁ h₂) := by
  simp [findKey, findKey?_cons_of_false h₂]

theorem findKey_beq [BEq α] {l : AssocList α β} {a : α} {h : l.contains a} : l.findKey a h == a := by
  induction l
  · simp at h
  · next k v t ih =>
    cases h' : k == a
    · rw [findKey_cons_of_false h']
      exact @ih (contains_of_contains_cons h h')
    · rwa [findKey_cons_of_beq h']

def find [BEq α] (l : AssocList α β) (a : α) (h : l.contains a) : β :=
  (l.find? a).get <| (contains_eq_isSome_find? l).symm.trans h

theorem find?_eq_some_find [BEq α] {l : AssocList α β} {a : α} (h : l.contains a) :
    l.find? a = some (l.find a h) := by
  simp [find]

theorem find_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).find a (contains_cons_of_beq h) = v := by
  simp [find, find?_cons_of_true h]

@[simp]
theorem find_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.cons k v).find k contains_cons_self = v :=
  find_cons_of_beq BEq.refl

theorem find_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β} {h₁ : (l.cons k v).contains a}
    (h₂ : (k == a) = false) : (l.cons k v).find a h₁ = l.find a (contains_of_contains_cons h₁ h₂) := by
  simp [find, find?_cons_of_false h₂]

def replace [BEq α] (a : α) (b : β) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then cons k b l else cons k v (replace a b l)

@[simp] theorem replace_nil [BEq α] {a : α} {b : β} : nil.replace a b = nil := rfl
theorem replace_cons [BEq α] {l : AssocList α β} {k a : α} {v b : β} :
    (l.cons k v).replace a b = bif k == a then l.cons k b else (l.replace a b).cons k v := rfl

theorem replace_cons_of_true [BEq α] {l : AssocList α β} {k a : α} {v b : β} (h : k == a) :
    (l.cons k v).replace a b = l.cons k b := by
  simp [replace, h]

theorem replace_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v b : β} (h : (k == a) = false) :
    (l.cons k v).replace a b = (l.replace a b).cons k v := by
  simp [replace, h]

theorem replace_of_contains_eq_false [BEq α] {l : AssocList α β} {a : α} {b : β} (h : l.contains a = false) :
    l.replace a b = l := by
  induction l
  · simp
  · next k v l ih =>
    rw [contains_cons_eq_false] at h
    rw [replace_cons_of_false h.1, ih h.2]

theorem findEntry?_replace_of_contains_eq_false [BEq α] {l : AssocList α β} {k a : α} {b : β}
    (hl : l.contains a = false) : (l.replace a b).findEntry? k = l.findEntry? k := by
  rw [replace_of_contains_eq_false hl]

theorem findEntry?_replace_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β}
    (h : (k == a) = false) : (l.replace a b).findEntry? k = l.findEntry? k := by
  induction l
  · simp
  · next k' v' l ih =>
    cases h' : k' == a
    · rw [replace_cons_of_false h', findEntry?_cons, findEntry?_cons, ih]
    · rw [replace_cons_of_true h']
      have hk : (k' == k) = false := by
        -- TODO: extract this out and make it nicer
        rw [Bool.eq_false_iff]
        intro hx
        apply Bool.eq_false_iff.1 h
        exact BEq.trans (BEq.symm hx) h'
      simp [findEntry?_cons_of_false hk]

theorem findEntry?_replace_of_true [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β} (hl : l.contains a = true)
    (h : k == a) : (l.replace a b).findEntry? k = some (l.findKey a hl, b) := by
  induction l
  · simp at hl
  · next k' v' l ih =>
    cases hk'a : k' == a
    · rw [replace_cons_of_false hk'a]
      have hk'k : (k' == k) = false := by

        -- TODO: extract this out and make it nicer
        rw [Bool.eq_false_iff]
        intro hx
        apply Bool.eq_false_iff.1 hk'a
        exact BEq.trans hx h
      rw [findEntry?_cons_of_false hk'k]
      have hl'₂ : l.contains a = true := contains_of_contains_cons hl hk'a
      rw [findKey_cons_of_false hk'a, ih hl'₂]
    · rw [replace_cons_of_true hk'a]
      have hkk' : k' == k := by
        exact BEq.trans hk'a (BEq.symm h)
      rw [findEntry?_cons_of_true hkk', findKey_cons_of_beq hk'a]

theorem find?_replace_of_contains_eq_false [BEq α] {l : AssocList α β} {k a : α} {b : β}
    (hl : l.contains a = false) : (l.replace a b).find? k = l.find? k := by
  simp [find?_eq_findEntry?, findEntry?_replace_of_contains_eq_false hl]

theorem find?_replace_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β}
    (h : (k == a) = false) : (l.replace a b).find? k = l.find? k := by
  simp [find?_eq_findEntry?, findEntry?_replace_of_false h]

theorem find?_replace_of_true [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β}
    (hl : l.contains a = true) (h : k == a) : (l.replace a b).find? k = some b := by
  simp [find?_eq_findEntry?, findEntry?_replace_of_true hl h]

theorem findKey?_replace_of_contains_eq_false [BEq α] {l : AssocList α β} {k a : α} {b : β}
    (hl : l.contains a = false) : (l.replace a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replace_of_contains_eq_false hl]

theorem findKey?_replace_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β}
    (h : (k == a) = false) : (l.replace a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replace_of_false h]

theorem findKey?_replace_of_true [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β}
    (hl : l.contains a = true) (h : (k == a)) : (l.replace a b).findKey? k = some (l.findKey a hl) := by
  simp [findKey?_eq_findEntry?, findEntry?_replace_of_true hl h]

theorem contains_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {a b : α} (hla : l.contains a) (hab : a == b) :
    l.contains b := by
  induction l
  · simp at hla
  · next k v l ih =>
    rw [contains_cons_eq_true]
    rcases (contains_cons_eq_true.1 hla) with (hla|hla)
    · exact Or.inl (BEq.trans hla hab)
    · exact Or.inr (ih hla)

theorem contains_eq_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {a b : α} (h : a == b) :
    l.contains a = l.contains b :=
  Bool.eq_iff_iff.2 ⟨fun hl => contains_of_beq hl h, fun hl => contains_of_beq hl (BEq.symm h)⟩

@[simp]
theorem contains_replace [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {b : β} :
    (l.replace k v).contains a = l.contains a := by
  simp only [contains_eq_isSome_findEntry?]
  cases hl : l.contains k
  · rw [findEntry?_replace_of_contains_eq_false hl]
  · cases h : a == k
    · rw [findEntry?_replace_of_false h]
    · rw [findEntry?_replace_of_true hl h]
      have ha : l.contains a := contains_of_beq hl (BEq.symm h)
      rw [Option.isSome_some, ← contains_eq_isSome_findEntry?, ha]

def erase [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil => nil
  | cons k v l => bif k == a then l else cons k v (l.erase a)

@[simp] theorem erase_nil [BEq α] {a : α} : (nil : AssocList α β).erase a = nil := rfl
theorem erase_cons [BEq α] {l : AssocList α β} {k a : α} {v : β} :
    (l.cons k v).erase a = bif k == a then l else cons k v (l.erase a) := rfl

theorem erase_cons_of_beq [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.cons k v).erase a = l :=
  by simp [erase_cons, h]

@[simp]
theorem erase_cons_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.cons k v).erase k = l :=
  erase_cons_of_beq BEq.refl

theorem erase_cons_of_false [BEq α] {l : AssocList α β} {k a : α} {v : β} (h : (k == a) = false) :
    (l.cons k v).erase a = (l.erase a).cons k v := by
  simp [erase_cons, h]

/--
`O(n)`. Convert an `AssocList α β` to the list of keys in appearance order.
-/
def keys : AssocList α β → List α
  | nil => []
  | cons k _ l => k :: (keys l)

@[simp] theorem keys_nil : (nil : AssocList α β).keys = [] := rfl
@[simp] theorem keys_cons {l : AssocList α β} {k : α} {v : β} : (l.cons k v).keys = k :: l.keys := rfl

@[simp]
theorem keys_replace [BEq α] {l : AssocList α β} {a : α} {b : β} : (l.replace a b).keys = l.keys := by
  induction l
  · simp
  · next k v t ih =>
    simp [replace_cons, cond_eq_if, apply_ite keys, ih]

theorem contains_eq_keys_contains [BEq α] [EquivBEq α] {l : AssocList α β} {a : α} :
    l.contains a = l.keys.contains a := by
  induction l
  · rfl
  · next k _ l ih =>
    simp [ih, BEq.comm]

/-- The well-formedness predicate for `AssocList` says that keys are pairwise distinct. -/
structure WF [BEq α] (l : AssocList α β) : Prop where
  distinct : l.keys.Pairwise fun a b => (a == b) = false

theorem WF.nil [BEq α] : (nil : AssocList α β).WF :=
  ⟨by simp⟩

theorem WF_of_keys_eq [BEq α] {l l' : AssocList α β} (h : l.keys = l'.keys) : l.WF → l'.WF :=
  fun ⟨h'⟩ => ⟨h ▸ h'⟩

theorem contains_iff_exists [BEq α] [EquivBEq α] {l : AssocList α β} {a : α} :
    l.contains a ↔ ∃ a' ∈ l.keys, a == a' := by
  rw [contains_eq_keys_contains, List.contains_iff_exists_beq]

theorem contains_eq_false_iff_forall [BEq α] [EquivBEq α] {l : AssocList α β} {a : α} :
    (l.contains a) = false ↔ ∀ a' ∈ l.keys, (a == a') = false := by
  simp only [Bool.eq_false_iff, ne_eq, contains_iff_exists, not_exists, not_and]

@[simp]
theorem WF_cons_iff [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.cons k v).WF ↔ l.WF ∧ (l.contains k) = false := by
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨⟨h₁⟩, h₂⟩ => ⟨?_⟩⟩
  · rw [keys_cons, List.pairwise_cons] at h
    exact ⟨⟨h.2⟩, contains_eq_false_iff_forall.2 h.1⟩
  · rw [keys_cons, List.pairwise_cons, ← contains_eq_false_iff_forall]
    exact ⟨h₂, h₁⟩

theorem WF_replace [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} : l.WF → (l.replace k v).WF :=
  WF_of_keys_eq keys_replace.symm

def insert [BEq α] (l : AssocList α β) (k : α) (v : β) : AssocList α β :=
  bif l.contains k then l.replace k v else l.cons k v

theorem insert_of_contains [BEq α] {l : AssocList α β} {k : α} {v : β} (h : l.contains k) :
    l.insert k v = l.replace k v := by
  simp [insert, h]

theorem insert_of_contains_eq_false [BEq α] {l : AssocList α β} {k : α} {v : β} (h : l.contains k = false) :
    l.insert k v = l.cons k v := by
  simp [insert, h]

theorem WF_insert [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} (h : l.WF) : (l.insert k v).WF := by
  cases h' : l.contains k
  · rw [insert_of_contains_eq_false h', WF_cons_iff]
    exact ⟨h, h'⟩
  · rw [insert_of_contains h']
    exact WF_replace h

theorem find?_insert_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.insert k v).find? a = some v := by
  cases h' : l.contains k
  · rw [insert_of_contains_eq_false h', find?_cons_of_true h]
  · rw [insert_of_contains h', find?_replace_of_true h' (BEq.symm h)]

theorem find?_insert_of_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.insert k v).find? k = some v :=
  find?_insert_of_beq BEq.refl

theorem find?_insert_of_false [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β} (h : (k == a) = false) :
    (l.insert k v).find? a = l.find? a := by
  cases h' : l.contains k
  · rw [insert_of_contains_eq_false h', find?_cons_of_false h]
  · rw [insert_of_contains h', find?_replace_of_false (BEq.symm_false h)]

-- TODO: would this be a reasonable simp lemma?
theorem find?_insert [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β} :
    (l.insert k v).find? a = bif k == a then some v else l.find? a := by
  cases h : k == a
  · simp [find?_insert_of_false h, h]
  · simp [find?_insert_of_beq h, h]

@[simp]
theorem contains_insert [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β} :
    (l.insert k v).contains a = ((k == a) || l.contains a) := by
  rw [contains_eq_isSome_find?, contains_eq_isSome_find?, find?_insert]
  cases k == a
  · simp
  · simp

theorem contains_insert_of_beq [BEq α] [EquivBEq α] {l : AssocList α β} {k a : α} {v : β} (h : k == a) :
    (l.insert k v).contains a := by
  simp [h]

theorem contains_insert_self [BEq α] [EquivBEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.insert k v).contains k :=
  contains_insert_of_beq BEq.refl

-- TODO: results about findEntry?+insert and findKey?+insert

-- TODO: lots of results about erase, including contains+erase, erase+insert and erase+WF

end AssocList

end Lean
