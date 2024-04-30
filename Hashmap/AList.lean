/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.BEq
import Std.Data.List.Lemmas
import Std.Data.List.Perm
import Hashmap.LawfulHashable
import Hashmap.Or

universe v u

variable {α : Type u} {β : α → Type v}

section
variable {α : Type u} {β : Type v}

theorem apply_bif (f : α → β) {b : Bool} {a a' : α} :
    f (bif b then a else a') = bif b then f a else f a' := by
  cases b <;> simp

@[simp]
theorem bif_const {b : Bool} {a : α} : (bif b then a else a) = a := by
  cases b <;> simp

end

namespace List

@[elab_as_elim]
theorem assoc_induction {motive : List (Σ a, β a) → Prop} (nil : motive [])
    (cons : (k : α) → (v : β k) → (tail : List (Σ a, β a)) → motive tail → motive (⟨k, v⟩ :: tail)) :
    (t : List (Σ a, β a)) → motive t
  | [] => nil
  | ⟨_, _⟩ :: _ => cons _ _ _ (assoc_induction nil cons _)

def findEntry? [BEq α] (a : α) : List (Σ a, β a) → Option (Σ a, β a)
  | [] => none
  | ⟨k, v⟩ :: l => bif k == a then some ⟨k, v⟩ else findEntry? a l

@[simp] theorem findEntry?_nil [BEq α] {a : α} : ([] : List (Σ a, β a)).findEntry? a = none := rfl
theorem findEntry?_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).findEntry? a = bif k == a then some ⟨k, v⟩ else l.findEntry? a := rfl

theorem findEntry?_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).findEntry? a = some ⟨k, v⟩ := by
  simp [findEntry?, h]

theorem findEntry?_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).findEntry? a = l.findEntry? a := by
  simp [findEntry?, h]

-- TODO also provide this for findKey and findValue
@[simp]
theorem findEntry?_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).findEntry? k = some ⟨k, v⟩ :=
  findEntry?_cons_of_true BEq.refl

theorem findEntry?_eq_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.findEntry? a = l.findEntry? a' := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h' : k == a
    · have h₂ : (k == a') = false := BEq.neq_of_neq_of_beq h' h
      rw [findEntry?_cons_of_false h', findEntry?_cons_of_false h₂, ih]
    · rw [findEntry?_cons_of_true h', findEntry?_cons_of_true (BEq.trans h' h)]

section

variable {β : Type v}

def findValue? [BEq α] (a : α) : List ((_ : α) × β) → Option β
  | [] => none
  | ⟨k, v⟩ :: l => bif k == a then some v else l.findValue? a

@[simp] theorem findValue?_nil [BEq α] {a : α} : ([] : List ((_ : α) × β)).findValue? a = none := rfl
theorem findValue?_cons [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} :
    (⟨k, v⟩ :: l).findValue? a = bif k == a then some v else l.findValue? a := rfl

theorem findValue?_cons_of_true [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    (⟨k, v⟩ :: l).findValue? a = some v := by
  simp [findValue?, h]

theorem findValue?_cons_of_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).findValue? a = l.findValue? a := by
  simp [findValue?, h]

theorem findValue?_eq_findEntry? [BEq α] {l : List ((_ : α) × β)} {a : α} :
    l.findValue? a = (l.findEntry? a).map (·.2) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, findValue?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, findValue?_cons_of_true h, Option.map_some']

theorem findValue?_eq_of_beq [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {a a' : α} (h : a == a') :
    l.findValue? a = l.findValue? a' := by
  simp [findValue?_eq_findEntry?, findEntry?_eq_of_beq h]

end

def findKey? [BEq α] (a : α) : List (Σ a, β a) → Option α
  | nil => none
  | ⟨k, _⟩ :: l => bif k == a then some k else l.findKey? a

@[simp] theorem findKey?_nil [BEq α] {a : α} : (nil : List (Σ a, β a)).findKey? a = none := rfl
theorem findKey?_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).findKey? a = bif k == a then some k else l.findKey? a := rfl

theorem findKey?_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).findKey? a = some k := by
  simp [findKey?, h]

theorem findKey?_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).findKey? a = l.findKey? a := by
  simp [findKey?, h]

theorem findKey?_eq_findEntry? [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.findKey? a = (l.findEntry? a).map (·.1) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, findKey?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, findKey?_cons_of_true h, Option.map_some']

theorem findKey?_eq_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.findKey? a = l.findKey? a' := by
  simp [findKey?_eq_findEntry?, findEntry?_eq_of_beq h]

def containsKey [BEq α] (a : α) : List (Σ a, β a) → Bool
  | nil => false
  | ⟨k, _⟩ :: l => k == a || l.containsKey a

@[simp] theorem containsKey_nil [BEq α] {a : α} : (nil : List (Σ a, β a)).containsKey a = false := rfl
@[simp] theorem containsKey_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).containsKey a = (k == a || l.containsKey a) := rfl

-- TODO: is this still needed?
theorem containsKey_eq_foldl [BEq α] {a : α} {l : List (Σ a, β a)} :
    l.containsKey a = l.foldl (fun acc e => acc || e.1 == a) false := by
  suffices ∀ b, (b || l.containsKey a) = l.foldl (fun acc e => acc || e.1 == a) b by simpa using this false
  induction l using assoc_induction
  · simp
  · next k v t ih =>
    skip
    simp
    intro b
    rw [← Bool.or_assoc, ih]

theorem containsKey_cons_eq_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    ((⟨k, v⟩ :: l).containsKey a = false) ↔ ((k == a) = false) ∧ (l.containsKey a = false) := by
  rw [Bool.eq_iff_iff]
  simp [containsKey_cons, not_or]

theorem containsKey_cons_eq_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    ((⟨k, v⟩ :: l).containsKey a) ↔ (k == a) ∨ (l.containsKey a) := by
  rw [Bool.eq_iff_iff]
  simp [containsKey_cons]

theorem containsKey_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).containsKey a := containsKey_cons_eq_true.2 <| Or.inl h

@[simp]
theorem containsKey_cons_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).containsKey k := containsKey_cons_of_beq BEq.refl

theorem containsKey_cons_of_containsKey [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : l.containsKey a) :
    (⟨k, v⟩ :: l).containsKey a := containsKey_cons_eq_true.2 <| Or.inr h

theorem containsKey_of_containsKey_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h₁ : (⟨k, v⟩ :: l).containsKey a)
    (h₂ : (k == a) = false) : l.containsKey a := by
  rcases (containsKey_cons_eq_true.1 h₁) with (h|h)
  · exact False.elim (Bool.eq_false_iff.1 h₂ h)
  · exact h

theorem containsKey_eq_isSome_findEntry? [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = (l.findEntry? a).isSome := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · simp [findEntry?_cons_of_false h, h, ih]
    · simp [findEntry?_cons_of_true h, h]

-- TODO: provide for findKey? and findValue?
theorem findEntry?_eq_none [BEq α] {l : List (Σ a, β a)} {a : α} (h : (l.containsKey a) = false) :
    l.findEntry? a = none := by
  rwa [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, ← containsKey_eq_isSome_findEntry?]

-- TODO
@[simp] theorem Option.isSome_map (α : Type u) (β : Type v) (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by
  cases o <;> simp

theorem containsKey_eq_isSome_findValue? {β : Type v} [BEq α] {l : List ((_ : α) × β)} {a : α} :
    l.containsKey a = (l.findValue? a).isSome := by
  simp [containsKey_eq_isSome_findEntry?, findValue?_eq_findEntry?]

theorem containsKey_eq_isSome_findKey? [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = (l.findKey? a).isSome := by
  simp [containsKey_eq_isSome_findEntry?, findKey?_eq_findEntry?]

theorem containsKey_eq_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a b : α} (h : a == b) :
    l.containsKey a = l.containsKey b := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eq_of_beq h]

theorem containsKey_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a b : α} (hla : l.containsKey a) (hab : a == b) :
    l.containsKey b := by
  rwa [← containsKey_eq_of_beq hab]

def findEntry [BEq α] (l : List (Σ a, β a)) (a : α) (h : l.containsKey a) : Σ a, β a :=
  (l.findEntry? a).get <| containsKey_eq_isSome_findEntry?.symm.trans h

theorem findEntry?_eq_some_findEntry [BEq α] {l : List (Σ a, β a)} {a : α} (h : l.containsKey a) :
    l.findEntry? a = some (l.findEntry a h) := by
  simp [findEntry]

theorem findEntry_eq_of_findEntry?_eq_some [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : l.findEntry? a = some ⟨k, v⟩) {h'} : l.findEntry a h' = ⟨k, v⟩ := by
  simp [findEntry, h]

theorem findEntry_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).findEntry a (containsKey_cons_of_beq (v := v) h) = ⟨k, v⟩ := by
  simp [findEntry, findEntry?_cons_of_true h]

@[simp]
theorem findEntry_cons_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).findEntry k containsKey_cons_self = ⟨k, v⟩ :=
  findEntry_cons_of_beq BEq.refl

theorem findEntry_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {h₁ : (⟨k, v⟩ :: l).containsKey a}
    (h₂ : (k == a) = false) :
    (⟨k, v⟩ :: l).findEntry a h₁ = l.findEntry a (containsKey_of_containsKey_cons (v := v) h₁ h₂) := by
  simp [findEntry, findEntry?_cons_of_false h₂]

def findKey [BEq α] (l : List (Σ a, β a)) (a : α) (h : l.containsKey a) : α :=
  (l.findKey? a).get <| containsKey_eq_isSome_findKey?.symm.trans h

theorem findKey?_eq_some_findKey [BEq α] {l : List (Σ a, β a)} {a : α} (h : l.containsKey a) :
    l.findKey? a = some (l.findKey a h) := by
  simp [findKey]

theorem findKey_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).findKey a (containsKey_cons_of_beq (v := v) h) = k := by
  simp [findKey, findKey?_cons_of_true h]

@[simp]
theorem findKey_cons_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).findKey k containsKey_cons_self = k :=
  findKey_cons_of_beq BEq.refl

theorem findKey_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {h₁ : (⟨k, v⟩ :: l).containsKey a}
    (h₂ : (k == a) = false) : (⟨k, v⟩ :: l).findKey a h₁ = l.findKey a (containsKey_of_containsKey_cons (v := v) h₁ h₂) := by
  simp [findKey, findKey?_cons_of_false h₂]

theorem findKey_beq [BEq α] {l : List (Σ a, β a)} {a : α} {h : l.containsKey a} : l.findKey a h == a := by
  induction l using assoc_induction
  · simp at h
  · next k v t ih =>
    cases h' : k == a
    · rw [findKey_cons_of_false h']
      exact @ih (containsKey_of_containsKey_cons h h')
    · rwa [findKey_cons_of_beq h']

section

variable {β : Type v}

def findValue [BEq α] (l : List ((_ : α) × β)) (a : α) (h : l.containsKey a) : β :=
  (l.findValue? a).get <| containsKey_eq_isSome_findValue?.symm.trans h

theorem findValue?_eq_some_find [BEq α] {l : List ((_ : α) × β)} {a : α} (h : l.containsKey a) :
    l.findValue? a = some (l.findValue a h) := by
  simp [findValue]

theorem findValue_cons_of_beq [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    (⟨k, v⟩ :: l).findValue a (containsKey_cons_of_beq (k := k) (v := v) h) = v := by
  simp [findValue, findValue?_cons_of_true h]

@[simp]
theorem findValue_cons_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (⟨k, v⟩ :: l).findValue k containsKey_cons_self = v :=
  findValue_cons_of_beq BEq.refl

theorem findValue_cons_of_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} {h₁ : (⟨k, v⟩ :: l).containsKey a}
    (h₂ : (k == a) = false) : (⟨k, v⟩ :: l).findValue a h₁ = l.findValue a (containsKey_of_containsKey_cons (k := k) (v := v) h₁ h₂) := by
  simp [findValue, findValue?_cons_of_false h₂]

end

def replaceEntry [BEq α] (a : α) (b : β a) : List (Σ a, β a) → List (Σ a, β a)
  | nil => nil
  | ⟨k, v⟩ :: l => bif k == a then ⟨a, b⟩ :: l else ⟨k, v⟩ :: replaceEntry a b l

@[simp] theorem replaceEntry_nil [BEq α] {a : α} {b : β a} : nil.replaceEntry a b = nil := rfl
theorem replaceEntry_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {b : β a} :
    (⟨k, v⟩ :: l).replaceEntry a b = bif k == a then ⟨a, b⟩ :: l else ⟨k, v⟩ :: l.replaceEntry a b := rfl

theorem replaceEntry_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {b : β a} (h : k == a) :
    (⟨k, v⟩ :: l).replaceEntry a b = ⟨a, b⟩ :: l := by
  simp [replaceEntry, h]

theorem replaceEntry_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {b : β a} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).replaceEntry a b = ⟨k, v⟩ :: l.replaceEntry a b := by
  simp [replaceEntry, h]

theorem replaceEntry_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {a : α} {b : β a} (h : l.containsKey a = false) :
    l.replaceEntry a b = l := by
  induction l
  · simp
  · next k v l ih =>
    rw [containsKey_cons_eq_false] at h
    rw [replaceEntry_cons_of_false h.1, ih h.2]

theorem findEntry?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).findEntry? k = l.findEntry? k := by
  rw [replaceEntry_of_containsKey_eq_false hl]

theorem findEntry?_replaceEntry_of_false [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replaceEntry a b).findEntry? k = l.findEntry? k := by
  induction l using assoc_induction
  · simp
  · next k' v' l ih =>
    cases h' : k' == a
    · rw [replaceEntry_cons_of_false h', findEntry?_cons, findEntry?_cons, ih]
    · rw [replaceEntry_cons_of_true h']
      have hk : (k' == k) = false := BEq.neq_of_beq_of_neq h' (BEq.symm_false h)
      simp [findEntry?_cons_of_false (BEq.symm_false h), findEntry?_cons_of_false hk]

theorem findEntry?_replaceEntry_of_true [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} (hl : l.containsKey a = true)
    (h : k == a) : (l.replaceEntry a b).findEntry? k = some ⟨a, b⟩ := by
  induction l using assoc_induction
  · simp at hl
  · next k' v' l ih =>
    cases hk'a : k' == a
    · rw [replaceEntry_cons_of_false hk'a]
      have hk'k : (k' == k) = false := BEq.neq_of_neq_of_beq hk'a (BEq.symm h)
      rw [findEntry?_cons_of_false hk'k]
      exact ih (containsKey_of_containsKey_cons hl hk'a)
    · rw [replaceEntry_cons_of_true hk'a, findEntry?_cons_of_true (BEq.symm h)]

theorem findEntry?_replaceEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).findEntry? k = bif l.containsKey a && k == a then some ⟨a, b⟩ else
      l.findEntry? k := by
  cases hl : l.containsKey a
  · simp [findEntry?_replaceEntry_of_containsKey_eq_false hl]
  · cases h : k == a
    · simp [findEntry?_replaceEntry_of_false h]
    · simp [findEntry?_replaceEntry_of_true hl h]

@[simp]
theorem length_replaceEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.replaceEntry k v).length = l.length := by
  induction l using assoc_induction <;> simp_all [replaceEntry_cons, apply_bif List.length]

section

variable {β : Type v}

theorem findValue?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).findValue? k = l.findValue? k := by
  simp [findValue?_eq_findEntry?, findEntry?_replaceEntry_of_containsKey_eq_false hl]

theorem findValue?_replaceEntry_of_false [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (h : (k == a) = false) : (l.replaceEntry a b).findValue? k = l.findValue? k := by
  simp [findValue?_eq_findEntry?, findEntry?_replaceEntry_of_false h]

theorem findValue?_replaceEntry_of_true [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (hl : l.containsKey a = true) (h : k == a) : (l.replaceEntry a b).findValue? k = some b := by
  simp [findValue?_eq_findEntry?, findEntry?_replaceEntry_of_true hl h]

end

theorem findKey?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replaceEntry_of_containsKey_eq_false hl]

theorem findKey?_replaceEntry_of_false [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replaceEntry a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replaceEntry_of_false h]

theorem findKey?_replaceEntry_of_true [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = true) (h : (k == a)) : (l.replaceEntry a b).findKey? k = some a := by
  simp [findKey?_eq_findEntry?, findEntry?_replaceEntry_of_true hl h]

theorem findKey?_replaceEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).findKey? k = bif l.containsKey a && k == a then some a else l.findKey? k := by
  cases hl : l.containsKey a
  · simp [findKey?_replaceEntry_of_containsKey_eq_false hl]
  · cases h : k == a
    · simp [findKey?_replaceEntry_of_false h]
    · simp [findKey?_replaceEntry_of_true hl h]

@[simp]
theorem containsKey_replaceEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).containsKey k = l.containsKey k := by
  cases h : l.containsKey a && k == a
  · rw [containsKey_eq_isSome_findKey?, findKey?_replaceEntry, h, cond_false, containsKey_eq_isSome_findKey?]
  · rw [containsKey_eq_isSome_findKey?, findKey?_replaceEntry, h, cond_true, Option.isSome_some, Eq.comm]
    rw [Bool.and_eq_true] at h
    exact containsKey_of_beq h.1 (BEq.symm h.2)

def eraseKey [BEq α] (a : α) : List (Σ a, β a) → List (Σ a, β a)
  | nil => nil
  | ⟨k, v⟩ :: l => bif k == a then l else ⟨k, v⟩ :: l.eraseKey a

@[simp] theorem eraseKey_nil [BEq α] {a : α} : (nil : List (Σ a, β a)).eraseKey a = nil := rfl
theorem eraseKey_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).eraseKey a = bif k == a then l else ⟨k, v⟩ :: l.eraseKey a := rfl

theorem eraseKey_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).eraseKey a = l :=
  by simp [eraseKey_cons, h]

@[simp]
theorem eraseKey_cons_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).eraseKey k = l :=
  eraseKey_cons_of_beq BEq.refl

theorem eraseKey_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).eraseKey a = ⟨k, v⟩ :: l.eraseKey a := by
  simp [eraseKey_cons, h]

-- TODO: eraseKey+replaceEntry

def keys : List (Σ a, β a) → List α
  | nil => []
  | ⟨k, _⟩ :: l => k :: (keys l)

@[simp] theorem keys_nil : (nil : List (Σ a, β a)).keys = [] := rfl
@[simp] theorem keys_cons {l : List (Σ a, β a)} {k : α} {v : β k} : (⟨k, v⟩ :: l).keys = k :: l.keys := rfl

theorem keys_eq_map (l : List (Σ a, β a)) : l.keys = l.map (·.1) := by
  induction l using assoc_induction <;> simp_all

theorem containsKey_eq_keys_containsKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = l.keys.contains a := by
  induction l using assoc_induction
  · rfl
  · next k _ l ih =>
    simp [ih, BEq.comm]

theorem containsKey_eq_true_iff_exists_mem [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = true ↔ ∃ p ∈ l, p.1 == a := by
  induction l using assoc_induction <;> simp_all

/-- The well-formedness predicate for `AssocList` says that keys are pairwise distinct. -/
structure WF [BEq α] (l : List (Σ a, β a)) : Prop where
  distinct : l.keys.Pairwise fun a b => (a == b) = false

@[simp]
theorem WF_nil [BEq α] : (nil : List (Σ a, β a)).WF :=
  ⟨by simp⟩

open List

theorem WF_of_perm_keys [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)}
    (h : l'.keys ~ l.keys) : l.WF → l'.WF
  | ⟨h'⟩ => ⟨h'.perm h.symm BEq.symm_false⟩

theorem WF_of_perm [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} (h : l' ~ l) :
    l.WF → l'.WF := by
  apply WF_of_perm_keys
  rw [keys_eq_map, keys_eq_map]
  exact h.map _

theorem WF_congr [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} (h : l ~ l') :
    l.WF ↔ l'.WF :=
  ⟨WF_of_perm h.symm, WF_of_perm h⟩

theorem WF_of_sublist_keys [BEq α] {l l' : List (Σ a, β a)} (h : l'.keys <+ l.keys) : l.WF → l'.WF :=
  fun ⟨h'⟩ => ⟨h'.sublist h⟩

theorem WF_of_keys_eq [BEq α] {l l' : List (Σ a, β a)} (h : l.keys = l'.keys) : l.WF → l'.WF :=
  WF_of_sublist_keys (h ▸ Sublist.refl _)

-- TODO
theorem List.contains_iff_exists_mem_beq [BEq α] (l : List α) (a : α) : l.contains a ↔ ∃ a' ∈ l, a == a' := by
  induction l <;> simp_all

theorem containsKey_iff_exists [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a ↔ ∃ a' ∈ l.keys, a == a' := by
  rw [containsKey_eq_keys_containsKey, List.contains_iff_exists_mem_beq]

theorem containsKey_eq_false_iff_forall [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {a : α} :
    (l.containsKey a) = false ↔ ∀ a' ∈ l.keys, (a == a') = false := by
  simp only [Bool.eq_false_iff, ne_eq, containsKey_iff_exists, not_exists, not_and]

@[simp]
theorem WF_cons_iff [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).WF ↔ l.WF ∧ (l.containsKey k) = false := by
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨⟨h₁⟩, h₂⟩ => ⟨?_⟩⟩
  · rw [keys_cons, List.pairwise_cons] at h
    exact ⟨⟨h.2⟩, containsKey_eq_false_iff_forall.2 h.1⟩
  · rw [keys_cons, List.pairwise_cons, ← containsKey_eq_false_iff_forall]
    exact ⟨h₂, h₁⟩

theorem WF.tail [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).WF → l.WF :=
  fun h => (WF_cons_iff.mp h).1

theorem WF.containsKey_eq_false [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).WF → l.containsKey k = false :=
  fun h => (WF_cons_iff.mp h).2

theorem WF_cons [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.containsKey k = false) :
    l.WF → (⟨k, v⟩ :: l).WF :=
  fun h' => WF_cons_iff.mpr ⟨h', h⟩

theorem WF_replaceEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.WF) : (l.replaceEntry k v).WF := by
  induction l using assoc_induction
  · simp
  · next k' v' l ih =>
    rw [WF_cons_iff] at h
    cases hk'k : k' == k
    · rw [replaceEntry_cons_of_false hk'k, WF_cons_iff]
      refine ⟨ih h.1, ?_⟩
      simpa using h.2
    · rw [replaceEntry_cons_of_true hk'k, WF_cons_iff]
      refine ⟨h.1, ?_⟩
      simpa [containsKey_eq_of_beq (BEq.symm hk'k)] using h.2

def insertEntry [BEq α] (l : List (Σ a, β a)) (k : α) (v : β k) : List (Σ a, β a) :=
  bif l.containsKey k then l.replaceEntry k v else ⟨k, v⟩ :: l

@[simp]
theorem insertEntry_nil [BEq α] {k : α} {v : β k} : ([] : List (Σ a, β a)).insertEntry k v = [⟨k, v⟩] := by
  simp [insertEntry]

theorem insertEntry_of_containsKey [BEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.containsKey k) :
    l.insertEntry k v = l.replaceEntry k v := by
  simp [insertEntry, h]

theorem insertEntry_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.containsKey k = false) :
    l.insertEntry k v = ⟨k, v⟩ :: l := by
  simp [insertEntry, h]

theorem WF_insertEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.WF) : (l.insertEntry k v).WF := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', WF_cons_iff]
    exact ⟨h, h'⟩
  · rw [insertEntry_of_containsKey h']
    exact WF_replaceEntry h

section

variable {β : Type v}

theorem findValue?_insertEntry_of_beq [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    (l.insertEntry k v).findValue? a = some v := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', findValue?_cons_of_true h]
  · rw [insertEntry_of_containsKey h', findValue?_replaceEntry_of_true h' (BEq.symm h)]

theorem findValue?_insertEntry_of_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (l.insertEntry k v).findValue? k = some v :=
  findValue?_insertEntry_of_beq BEq.refl

theorem findValue?_insertEntry_of_false [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : (k == a) = false) :
    (l.insertEntry k v).findValue? a = l.findValue? a := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', findValue?_cons_of_false h]
  · rw [insertEntry_of_containsKey h', findValue?_replaceEntry_of_false (BEq.symm_false h)]

-- TODO: would this be a reasonable simp lemma?
theorem findValue?_insertEntry [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} :
    (l.insertEntry k v).findValue? a = bif k == a then some v else l.findValue? a := by
  cases h : k == a
  · simp [findValue?_insertEntry_of_false h, h]
  · simp [findValue?_insertEntry_of_beq h, h]

end

-- TODO: Unify order in `bif k == a` vs. `bif a == k`.
theorem findKey?_insertEntry_of_containsKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : l.containsKey k) : (l.insertEntry k v).findKey? a = bif k == a then some k else l.findKey? a := by
  simp [insertEntry_of_containsKey h, findKey?_replaceEntry, h, BEq.comm]

theorem findKey?_insertEntry_of_containsKey_eq_false [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (hl : (l.containsKey k) = false) :
    (l.insertEntry k v).findKey? a = bif k == a then some k else l.findKey? a := by
  simp [insertEntry_of_containsKey_eq_false hl, findKey?_cons]

theorem findKey?_insertEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).findKey? a = bif k == a then some k else l.findKey? a := by
  cases hl : l.containsKey k
  · simp [findKey?_insertEntry_of_containsKey_eq_false hl, hl]
  · simp [findKey?_insertEntry_of_containsKey hl]

theorem findEntry?_insertEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).findEntry? a = bif k == a then some ⟨k, v⟩ else l.findEntry? a := by
  cases hl : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false hl, findEntry?_cons]
  · rw [insertEntry_of_containsKey hl, findEntry?_replaceEntry, hl, Bool.true_and, BEq.comm]

-- TODO: findEntry?_insertEntry_of_beq, findEntry?_insertEntry_of_beq_eq_false

@[simp]
theorem containsKey_insertEntry [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).containsKey a = ((k == a) || l.containsKey a) := by
  rw [containsKey_eq_isSome_findKey?, containsKey_eq_isSome_findKey?, findKey?_insertEntry]
  cases k == a
  · simp
  · simp

theorem containsKey_insertEntry_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (l.insertEntry k v).containsKey a := by
  simp [h]

@[simp]
theorem containsKey_insertEntry_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.insertEntry k v).containsKey k :=
  containsKey_insertEntry_of_beq BEq.refl

@[simp]
theorem keys_eraseKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} :
    (l.eraseKey k).keys = l.keys.erase k := by
  induction l using assoc_induction
  · rfl
  · next k' v' l ih =>
    simp only [eraseKey_cons, keys_cons, List.erase_cons]
    cases k' == k
    · simp [ih]
    · simp [ih]

theorem WF_eraseKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} : l.WF → (l.eraseKey k).WF := by
  apply WF_of_sublist_keys (by simpa using List.erase_sublist _ _)

theorem findEntry?_eraseKey_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.WF) :
    (l.eraseKey k).findEntry? k = none := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [eraseKey_cons_of_false h', findEntry?_cons_of_false h']
      exact ih (WF_cons_iff.1 h).1
    · rw [eraseKey_cons_of_beq h', ← Option.not_isSome_iff_eq_none, Bool.not_eq_true,
        ← containsKey_eq_isSome_findEntry?, ← containsKey_eq_of_beq h']
      exact (WF_cons_iff.1 h).2

theorem findEntry?_eraseKey_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.eraseKey k).findEntry? a = none := by
  rw [← findEntry?_eq_of_beq hka, findEntry?_eraseKey_self hl]

theorem findEntry?_eraseKey_of_false [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.eraseKey k).findEntry? a = l.findEntry? a := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [eraseKey_cons_of_false h']
      cases h'' : k' == a
      · rw [findEntry?_cons_of_false h'', ih, findEntry?_cons_of_false h'']
      · rw [findEntry?_cons_of_true h'', findEntry?_cons_of_true h'']
    · rw [eraseKey_cons_of_beq h']
      have hx : (k' == a) = false := BEq.neq_of_beq_of_neq h' hka
      rw [findEntry?_cons_of_false hx]

theorem findEntry?_eraseKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.WF) :
    (l.eraseKey k).findEntry? a = bif k == a then none else l.findEntry? a := by
  cases h : k == a
  · simp [findEntry?_eraseKey_of_false h, h]
  · simp [findEntry?_eraseKey_of_beq hl h, h]

section

variable {β : Type v}

-- TODO
theorem findValue?_eraseKey_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α} (h : l.WF) :
    (l.eraseKey k).findValue? k = none := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey_self h]

theorem findValue?_eraseKey_of_beq [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.eraseKey k).findValue? a = none := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey_of_beq hl hka]

theorem findValue?_eraseKey_of_false [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    (hka : (k == a) = false) : (l.eraseKey k).findValue? a = l.findValue? a := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey_of_false hka]

theorem findValue?_eraseKey [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k a : α} (hl : l.WF) :
    (l.eraseKey k).findValue? a = bif k == a then none else l.findValue? a := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey hl, apply_bif (Option.map _)]

end

theorem findKey?_eraseKey_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.WF) :
    (l.eraseKey k).findKey? k = none := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey_self h]

theorem findKey?_eraseKey_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.eraseKey k).findKey? a = none := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey_of_beq hl hka]

theorem findKey?_eraseKey_of_false [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.eraseKey k).findKey? a = l.findKey? a := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey_of_false hka]

theorem findKey?_eraseKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.WF) :
    (l.eraseKey k).findKey? a = bif k == a then none else l.findKey? a := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey hl, apply_bif (Option.map _)]

theorem containsKey_eraseKey_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.WF) :
    (l.eraseKey k).containsKey k = false := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eraseKey_self h]

theorem containsKey_eraseKey_of_beq [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.WF)
    (hka : k == a) : (l.eraseKey k).containsKey a = false := by
  rw [← containsKey_eq_of_beq hka, containsKey_eraseKey_self hl]

theorem containsKey_eraseKey_of_false [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.eraseKey k).containsKey a = l.containsKey a := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eraseKey_of_false hka]

theorem containsKey_eraseKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.WF) :
    (l.eraseKey k).containsKey a = bif k == a then false else l.containsKey a := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eraseKey hl, apply_bif Option.isSome]

-- TODO: Technically this should be true without assuming l.WF
theorem containsKey_of_containsKey_eraseKey [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.WF)
    (h : (l.eraseKey k).containsKey a) : l.containsKey a := by
  cases hka : k == a
  · rwa [containsKey_eraseKey_of_false hka] at h
  · simp [containsKey_eraseKey_of_beq hl hka] at h

theorem findEntry?_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} (hl : l.WF)
    (h : l ~ l') : l.findEntry? k = l'.findEntry? k := by
  induction h
  · simp
  · next p t₁ t₂ _ ih₂ =>
    rcases p with ⟨k', v'⟩
    simp only [findEntry?_cons, ih₂ hl.tail]
  · next p p' t =>
    rcases p with ⟨k₁, v₁⟩
    rcases p' with ⟨k₂, v₂⟩
    simp only [findEntry?_cons]
    cases h₂ : k₂ == k <;> cases h₁ : k₁ == k <;> try simp; done
    simp only [WF_cons_iff, containsKey_cons, Bool.or_eq_false_iff] at hl
    exact ((Bool.eq_false_iff.1 hl.2.1).elim (BEq.trans h₁ (BEq.symm h₂))).elim
  · next l₁ l₂ l₃ hl₁₂ _ ih₁ ih₂ => exact (ih₁ hl).trans (ih₂ (WF_of_perm (hl₁₂.symm) hl))

theorem containsKey_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} (hl : l.WF)
    (h : l ~ l') : l.containsKey k = l'.containsKey k := by
  simp only [containsKey_eq_isSome_findEntry?, findEntry?_of_perm hl h]

theorem perm_cons_findEntry [BEq α] {l : List (Σ a, β a)} {k : α} (h : l.containsKey k) :
    ∃ l', l ~ l.findEntry k h :: l' := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_true] at h
    cases hk : k' == k
    · obtain ⟨l', hl'⟩ := ih (h.resolve_left (Bool.not_eq_true _ ▸ hk))
      rw [findEntry_cons_of_false hk]
      exact ⟨⟨k', v'⟩ :: l', (hl'.cons _).trans (Perm.swap _ _ _)⟩
    · exact ⟨t, by rw [findEntry_cons_of_beq hk]⟩

theorem findEntry?_ext [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} (hl : l.WF) (hl' : l'.WF)
    (h : ∀ k, l.findEntry? k = l'.findEntry? k) : l ~ l' := by
  induction l using assoc_induction generalizing l'
  · induction l' using assoc_induction
    · rfl
    · next k _ _ _ => simpa using h k
  · next k v t ih =>
    have hl'k₁ : l'.findEntry? k = some ⟨k, v⟩ := by rw [← h, findEntry?_cons_self]
    have hl'k₂ : l'.containsKey k := by
      rw [containsKey_eq_isSome_findEntry?, hl'k₁, Option.isSome_some]
    obtain ⟨l'', hl''⟩ := perm_cons_findEntry hl'k₂
    rw [findEntry_eq_of_findEntry?_eq_some hl'k₁] at hl''
    suffices t ~ l'' from (this.cons _).trans hl''.symm
    apply ih hl.tail (WF_of_perm hl''.symm hl').tail
    intro k'
    cases hk' : k' == k
    · simpa only [findEntry?_of_perm hl' hl'', findEntry?_cons_of_false (BEq.symm_false hk')] using h k'
    · simp only [findEntry?_eq_of_beq hk']
      rw [findEntry?_eq_none hl.containsKey_eq_false,
          findEntry?_eq_none (WF_of_perm hl''.symm hl').containsKey_eq_false]

theorem replaceEntry_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} (k : α) (v : β k)
    (hl : l.WF) (h : l ~ l') : l.replaceEntry k v ~ l'.replaceEntry k v := by
  apply findEntry?_ext (WF_replaceEntry hl) (WF_replaceEntry (WF_of_perm h.symm hl))
  simp [findEntry?_replaceEntry, findEntry?_of_perm hl h, containsKey_of_perm hl h]

theorem insertEntry_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} {v : β k}
    (hl : l.WF) (h : l ~ l') : l.insertEntry k v ~ l'.insertEntry k v := by
  apply findEntry?_ext (WF_insertEntry hl) (WF_insertEntry (WF_of_perm h.symm hl))
  simp [findEntry?_insertEntry, findEntry?_of_perm hl h]

@[simp]
theorem findEntry?_append [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').findEntry? k = (l.findEntry? k).or (l'.findEntry? k) := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih => cases h : k' == k <;> simp_all [findEntry?_cons]

theorem findEntry?_append_of_containsKey_eq_false [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').findEntry? k = l.findEntry? k := by
  rw [findEntry?_append, findEntry?_eq_none h, Option.or_none]

@[simp]
theorem containsKey_append [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').containsKey k = (l.containsKey k || l'.containsKey k) := by
  simp [containsKey_eq_isSome_findEntry?]

theorem containsKey_append_of_not_contains_right [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α}
    (hl' : l'.containsKey k = false) : (l ++ l').containsKey k = l.containsKey k := by
  simp [hl']

theorem replaceEntry_append_of_containsKey_left [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α}
    {v : β k} (h : l.containsKey k) : (l ++ l').replaceEntry k v = l.replaceEntry k v ++ l' := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_true] at h
    cases h' : k' == k
    · simpa [replaceEntry_cons, h'] using ih (h.resolve_left (Bool.not_eq_true _ ▸ h'))
    · simp [replaceEntry_cons, h']

theorem insert_append_of_not_contains_right [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)}
    {k : α} {v : β k} (h' : l'.containsKey k = false) :
    (l ++ l').insertEntry k v = l.insertEntry k v ++ l' := by
  cases h : l.containsKey k
  · simp [insertEntry, containsKey_append, h, h']
  · simp [insertEntry, containsKey_append, h, h', replaceEntry_append_of_containsKey_left h]

-- TODO: Move to new file
structure HashesTo [BEq α] [Hashable α] (l : List (Σ a, β a)) (i : Nat) (size : Nat) : Prop where
  hash_self : ∀ p, p ∈ l → ((hash p.1).toUSize % size).toNat = i

@[simp]
theorem hashesTo_nil [BEq α] [Hashable α] {i : Nat} {size : Nat} :
    ([] : List (Σ a, β a)).HashesTo i size where
  hash_self := by simp

theorem hashesTo_cons [BEq α] [Hashable α] [LawfulHashable α] {i : Nat} {size : Nat} {l : List (Σ a, β a)} {k : α}
    {v : β k} (h : ((hash k).toUSize % size).toNat = i) :
    l.HashesTo i size → (⟨k, v⟩ :: l).HashesTo i size := by
  refine fun ⟨ih⟩ => ⟨fun k' hk => ?_⟩
  simp only [mem_cons] at hk
  rcases hk with (rfl|hk)
  · exact h
  · exact ih _ hk


-- TODO: results about combining modification operations

end List
