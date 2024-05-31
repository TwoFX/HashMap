/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.BEq
import Hashmap.List.Defs
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Perm
import Hashmap.LawfulHashable
import Hashmap.Or
import Hashmap.DHashMap.ForUpstream

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w}

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

/-- Search for an entry in a list of dependent pairs by key. -/
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

@[simp]
theorem findEntry?_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).findEntry? k = some ⟨k, v⟩ :=
  findEntry?_cons_of_true BEq.refl

theorem findEntry?_eq_some [BEq α] {l : List (Σ a, β a)} {a : α} {p : Σ a, β a}
    (h : l.findEntry? a = some p) : p.1 == a := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    cases h' : k' == a
    · rw [findEntry?_cons_of_false h'] at h
      exact ih h
    · rw [findEntry?_cons_of_true h', Option.some.injEq] at h
      obtain rfl := congrArg Sigma.fst h
      exact h'

theorem findEntry?_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
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

@[simp]
theorem findValue?_cons_self [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (⟨k, v⟩ :: l).findValue? k = some v :=
  findValue?_cons_of_true BEq.refl

theorem findValue?_eq_findEntry? [BEq α] {l : List ((_ : α) × β)} {a : α} :
    l.findValue? a = (l.findEntry? a).map (·.2) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, findValue?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, findValue?_cons_of_true h, Option.map_some']

theorem findValue?_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {a a' : α} (h : a == a') :
    l.findValue? a = l.findValue? a' := by
  simp [findValue?_eq_findEntry?, findEntry?_eq_of_beq h]

end

def findValueCast? [BEq α] [LawfulBEq α] (a : α) : List (Σ a, β a) → Option (β a)
  | [] => none
  | ⟨k, v⟩ :: l => if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else l.findValueCast? a

@[simp] theorem findValueCast?_nil [BEq α] [LawfulBEq α] {a : α} :
    ([] : List (Σ a, β a)).findValueCast? a = none := rfl
theorem findValueCast?_cons [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).findValueCast? a = if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else l.findValueCast? a := rfl

theorem findValueCast?_cons_of_true [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).findValueCast? a = some (cast (congrArg β (eq_of_beq h)) v) := by
  simp [findValueCast?, h]

theorem findValueCast?_cons_of_false [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : (k == a) = false) : (⟨k, v⟩ :: l).findValueCast? a = l.findValueCast? a := by
  simp [findValueCast?, h]

@[simp]
theorem findValueCast?_cons_self [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).findValueCast? k = some v := by
  rw [findValueCast?_cons_of_true BEq.refl, cast_eq]

def findValueWithCast? [BEq α] (a : α) (cast : ∀ {b}, b == a → β b → β a) : List (Σ a, β a) → Option (β a)
  | [] => none
  | ⟨k, v⟩ :: l => if h : k == a then some (cast h v) else l.findValueWithCast? a cast

@[simp] theorem findValueWithCast?_nil [BEq α] {a : α} {cast : ∀ {b}, b == a → β b → β a} :
    ([] : List (Σ a, β a)).findValueWithCast? a cast = none := rfl
theorem findValueWithCast?_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {cast : ∀ {b}, b == a → β b → β a} :
    (⟨k, v⟩ :: l).findValueWithCast? a cast = if h : k == a then some (cast h v) else l.findValueWithCast? a cast := rfl

theorem findValueWithCast?_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {cast : ∀ {b}, b == a → β b → β a} (h : k == a) :
    (⟨k, v⟩ :: l).findValueWithCast? a cast = some (cast h v) := by
  simp [findValueWithCast?, h]

theorem findValueWithCast?_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {cast : ∀ {b}, b == a → β b → β a}
    (h : (k == a) = false) : (⟨k, v⟩ :: l).findValueWithCast? a cast = l.findValueWithCast? a cast := by
  simp [findValueWithCast?, h]

@[simp]
theorem findValueWithCast?_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} {cast : ∀ {b}, b == k → β b → β k} :
    (⟨k, v⟩ :: l).findValueWithCast? k cast = some (cast BEq.refl v) := by
  rw [findValueWithCast?_cons_of_true BEq.refl]

section

variable {β : Type v}

/--
This is a strange dependent version of `Option.map` in which the mapping function is allowed to "know" about the
option that is being mapped...

It is even possible for `β` to be a type family depending on `o`, which is even worse, but it hints that this function
really isn't that different from `Option.rec` in some sense.
-/
def _root_.Option.dmap : (o : Option α) → (f : (a : α) → (o = some a) → β) → Option β
  | none, _ => none
  | some a, f => some (f a rfl)

@[simp] theorem _root_.Option.dmap_none (f : (a : α) → (none = some a) → β) : none.dmap f = none := rfl

@[simp] theorem _root_.Option.dmap_some (a : α) (f : (a' : α) → (some a = some a') → β) :
    (some a).dmap f = some (f a rfl) := rfl

theorem _root_.Option.dmap_congr {o o' : Option α} {f : (a : α) → (o = some a) → β} (h : o = o') :
    o.dmap f = o'.dmap (fun a h' => f a (h ▸ h')) := by
  cases h; rfl

@[simp]
theorem _root_.Option.isSome_dmap {o : Option α} {f : (a : α) → (o = some a) → β} :
    (o.dmap f).isSome = o.isSome := by
  cases o <;> rfl

-- TODO: this is not needed
theorem _root_.Option.dmap_or {o o' : Option α} (f : (a : α) → ((o.or o') = some a) → β) :
    (o.or o').dmap f = (o.dmap fun a h => f a (by rw [h, Option.or_some])).or (o'.dmap fun a h => match o with
      | none => f a (by rw [Option.none_or, h])
      | some a' => f a' (by rw [Option.or_some])) := by
  cases o <;> rfl

end

theorem findValueCast?_eq_findEntry? [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a : α} :
    l.findValueCast? a = (l.findEntry? a).dmap (fun p h => cast (congrArg β (eq_of_beq (findEntry?_eq_some h))) p.2) := by
  induction l using assoc_induction
  · simp
  · next k v t ih =>
    cases h : k == a
    · rw [findValueCast?_cons_of_false h, ih, Option.dmap_congr (findEntry?_cons_of_false h)]
    · rw [findValueCast?_cons_of_true h, Option.dmap_congr (findEntry?_cons_of_true h), Option.dmap_some]

theorem isSome_findValueCast?_eq_isSome_findEntry? [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a : α} :
    (l.findValueCast? a).isSome = (l.findEntry? a).isSome := by
  rw [findValueCast?_eq_findEntry?, Option.isSome_dmap]

theorem findValueCast?_congr [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.findValueCast? a = cast (congrArg _ (congrArg _ (eq_of_beq h).symm)) (l.findValueCast? a') := by
  obtain rfl := eq_of_beq h
  rw [cast_eq]

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

@[simp]
theorem findKey?_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).findKey? k = k :=
  findKey?_cons_of_true BEq.refl

theorem findKey?_eq_findEntry? [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.findKey? a = (l.findEntry? a).map (·.1) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [findEntry?_cons_of_false h, findKey?_cons_of_false h, ih]
    · rw [findEntry?_cons_of_true h, findKey?_cons_of_true h, Option.map_some']

theorem findKey?_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.findKey? a = l.findKey? a' := by
  simp [findKey?_eq_findEntry?, findEntry?_eq_of_beq h]

def containsKey [BEq α] (a : α) : List (Σ a, β a) → Bool
  | nil => false
  | ⟨k, _⟩ :: l => k == a || l.containsKey a

@[simp] theorem containsKey_nil [BEq α] {a : α} : (nil : List (Σ a, β a)).containsKey a = false := rfl
@[simp] theorem containsKey_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).containsKey a = (k == a || l.containsKey a) := rfl

theorem containsKey_cons_eq_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    ((⟨k, v⟩ :: l).containsKey a = false) ↔ ((k == a) = false) ∧ (l.containsKey a = false) := by
  simp [containsKey_cons, not_or]

theorem containsKey_cons_eq_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    ((⟨k, v⟩ :: l).containsKey a) ↔ (k == a) ∨ (l.containsKey a) := by
  simp [containsKey_cons]

theorem containsKey_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).containsKey a := containsKey_cons_eq_true.2 <| Or.inl h

@[simp]
theorem containsKey_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
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

@[simp]
theorem findEntry?_eq_none [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.findEntry? a = none ↔ l.containsKey a = false := by
  rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, ← containsKey_eq_isSome_findEntry?]

@[simp]
theorem findKey?_eq_none [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.findKey? a = none ↔ l.containsKey a = false := by
  rw [findKey?_eq_findEntry?, Option.map_eq_none', findEntry?_eq_none]

@[simp]
theorem findValue?_eq_none {β : Type v} [BEq α] {l : List ((_ : α) × β)} {a : α} :
    l.findValue? a = none ↔ l.containsKey a = false := by
  rw [findValue?_eq_findEntry?, Option.map_eq_none', findEntry?_eq_none]

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

theorem containsKey_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a b : α} (h : a == b) :
    l.containsKey a = l.containsKey b := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eq_of_beq h]

theorem containsKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a b : α} (hla : l.containsKey a) (hab : a == b) :
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
theorem findEntry_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
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
theorem findKey_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
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
theorem findValue_cons_self [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
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

theorem findEntry?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replaceEntry a b).findEntry? k = l.findEntry? k := by
  induction l using assoc_induction
  · simp
  · next k' v' l ih =>
    cases h' : k' == a
    · rw [replaceEntry_cons_of_false h', findEntry?_cons, findEntry?_cons, ih]
    · rw [replaceEntry_cons_of_true h']
      have hk : (k' == k) = false := BEq.neq_of_beq_of_neq h' (BEq.symm_false h)
      simp [findEntry?_cons_of_false (BEq.symm_false h), findEntry?_cons_of_false hk]

theorem findEntry?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} (hl : l.containsKey a = true)
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

theorem findEntry?_replaceEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).findEntry? k = bif l.containsKey a && k == a then some ⟨a, b⟩ else
      l.findEntry? k := by
  cases hl : l.containsKey a
  · simp [findEntry?_replaceEntry_of_containsKey_eq_false hl]
  · cases h : k == a
    · simp [findEntry?_replaceEntry_of_false h]
    · simp [findEntry?_replaceEntry_of_true hl h]

@[simp]
theorem length_replaceEntry [BEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.replaceEntry k v).length = l.length := by
  induction l using assoc_induction <;> simp_all [replaceEntry_cons, apply_bif List.length]

section

variable {β : Type v}

theorem findValue?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).findValue? k = l.findValue? k := by
  simp [findValue?_eq_findEntry?, findEntry?_replaceEntry_of_containsKey_eq_false hl]

theorem findValue?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (h : (k == a) = false) : (l.replaceEntry a b).findValue? k = l.findValue? k := by
  simp [findValue?_eq_findEntry?, findEntry?_replaceEntry_of_false h]

theorem findValue?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (hl : l.containsKey a = true) (h : k == a) : (l.replaceEntry a b).findValue? k = some b := by
  simp [findValue?_eq_findEntry?, findEntry?_replaceEntry_of_true hl h]

end

theorem findKey?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replaceEntry_of_containsKey_eq_false hl]

theorem findKey?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replaceEntry a b).findKey? k = l.findKey? k := by
  simp [findKey?_eq_findEntry?, findEntry?_replaceEntry_of_false h]

theorem findKey?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = true) (h : (k == a)) : (l.replaceEntry a b).findKey? k = some a := by
  simp [findKey?_eq_findEntry?, findEntry?_replaceEntry_of_true hl h]

theorem findKey?_replaceEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).findKey? k = bif l.containsKey a && k == a then some a else l.findKey? k := by
  cases hl : l.containsKey a
  · simp [findKey?_replaceEntry_of_containsKey_eq_false hl]
  · cases h : k == a
    · simp [findKey?_replaceEntry_of_false h]
    · simp [findKey?_replaceEntry_of_true hl h]

@[simp]
theorem containsKey_replaceEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
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
theorem eraseKey_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).eraseKey k = l :=
  eraseKey_cons_of_beq BEq.refl

theorem eraseKey_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).eraseKey a = ⟨k, v⟩ :: l.eraseKey a := by
  simp [eraseKey_cons, h]

theorem eraseKey_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k : α} (h : l.containsKey k = false) :
    l.eraseKey k = l := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_false_iff] at h
    rw [eraseKey_cons_of_false h.1, ih h.2]

theorem sublist_eraseKey [BEq α] {l : List (Σ a, β a)} {k : α} : (l.eraseKey k).Sublist l := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    rw [eraseKey_cons]
    cases k' == k
    · simpa
    · simp

theorem length_eraseKey [BEq α] {l : List (Σ a, β a)} {k : α} :
    (l.eraseKey k).length = bif l.containsKey k then l.length - 1 else l.length := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    rw [eraseKey_cons, containsKey_cons]
    cases k' == k
    · rw [cond_false, Bool.false_or, length_cons, ih]
      cases h : containsKey k t
      · simp
      · simp only [cond_true, Nat.succ_eq_add_one, length_cons, Nat.add_sub_cancel]
        rw [Nat.sub_add_cancel]
        cases t
        · simp at h
        · simp
    · simp

-- TODO: eraseKey+replaceEntry

@[simp] theorem keys_nil : ([] : List (Σ a, β a)).keys = [] := rfl
@[simp] theorem keys_cons {l : List (Σ a, β a)} {k : α} {v : β k} : (⟨k, v⟩ :: l).keys = k :: l.keys := rfl

theorem keys_eq_map (l : List (Σ a, β a)) : l.keys = l.map (·.1) := by
  induction l using assoc_induction <;> simp_all

theorem containsKey_eq_keys_contains [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = l.keys.contains a := by
  induction l using assoc_induction
  · rfl
  · next k _ l ih =>
    simp [ih, BEq.comm]

theorem containsKey_eq_true_iff_exists_mem [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = true ↔ ∃ p ∈ l, p.1 == a := by
  induction l using assoc_induction <;> simp_all

theorem containsKey_of_mem [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {p : Σ a, β a} (hp : p ∈ l) :
    l.containsKey p.1 :=
  containsKey_eq_true_iff_exists_mem.2 ⟨p, ⟨hp, BEq.refl⟩⟩

@[simp]
theorem DistinctKeys.nil [BEq α] : ([] : List (Σ a, β a)).DistinctKeys :=
  ⟨by simp⟩

open List

theorem DistinctKeys.perm_keys [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)}
    (h : l'.keys ~ l.keys) : l.DistinctKeys → l'.DistinctKeys
  | ⟨h'⟩ => ⟨h'.perm h.symm BEq.symm_false⟩

theorem DistinctKeys.perm [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} (h : l' ~ l) :
    l.DistinctKeys → l'.DistinctKeys := by
  apply DistinctKeys.perm_keys
  rw [keys_eq_map, keys_eq_map]
  exact h.map _

theorem DistinctKeys.congr [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} (h : l ~ l') :
    l.DistinctKeys ↔ l'.DistinctKeys :=
  ⟨fun h' => h'.perm h.symm, fun h' => h'.perm h⟩

theorem distinctKeys_of_sublist_keys [BEq α] {l : List (Σ a, β a)} {l' : List (Σ a, γ a)} (h : l'.keys <+ l.keys) : l.DistinctKeys → l'.DistinctKeys :=
  fun ⟨h'⟩ => ⟨h'.sublist h⟩

theorem DistinctKeys.of_keys_eq [BEq α] {l : List (Σ a, β a)} {l' : List (Σ a, γ a)} (h : l.keys = l'.keys) : l.DistinctKeys → l'.DistinctKeys :=
  distinctKeys_of_sublist_keys (h ▸ Sublist.refl _)

-- TODO
theorem List.contains_iff_exists_mem_beq [BEq α] (l : List α) (a : α) : l.contains a ↔ ∃ a' ∈ l, a == a' := by
  induction l <;> simp_all

theorem containsKey_iff_exists [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a ↔ ∃ a' ∈ l.keys, a == a' := by
  rw [containsKey_eq_keys_contains, List.contains_iff_exists_mem_beq]

theorem containsKey_eq_false_iff_forall_mem_keys [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a : α} :
    (l.containsKey a) = false ↔ ∀ a' ∈ l.keys, (a == a') = false := by
  simp only [Bool.eq_false_iff, ne_eq, containsKey_iff_exists, not_exists, not_and]

@[simp]
theorem distinctKeys_cons_iff [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).DistinctKeys ↔ l.DistinctKeys ∧ (l.containsKey k) = false := by
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨⟨h₁⟩, h₂⟩ => ⟨?_⟩⟩
  · rw [keys_cons, List.pairwise_cons] at h
    exact ⟨⟨h.2⟩, containsKey_eq_false_iff_forall_mem_keys.2 h.1⟩
  · rw [keys_cons, List.pairwise_cons, ← containsKey_eq_false_iff_forall_mem_keys]
    exact ⟨h₂, h₁⟩

theorem DistinctKeys.tail [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).DistinctKeys → l.DistinctKeys :=
  fun h => (distinctKeys_cons_iff.mp h).1

theorem DistinctKeys.containsKey_eq_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).DistinctKeys → l.containsKey k = false :=
  fun h => (distinctKeys_cons_iff.mp h).2

theorem DistinctKeys.cons [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.containsKey k = false) :
    l.DistinctKeys → (⟨k, v⟩ :: l).DistinctKeys :=
  fun h' => distinctKeys_cons_iff.mpr ⟨h', h⟩

theorem mem_iff_findEntry?_eq_some [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {p : Σ a, β a} (h : l.DistinctKeys) :
    p ∈ l ↔ l.findEntry? p.1 = some p := by
  induction l using assoc_induction
  · simp_all
  · next k v t ih =>
    simp only [mem_cons, findEntry?_cons, ih h.tail]
    refine ⟨?_, ?_⟩
    · rintro (rfl|hk)
      · simp
      · suffices (k == p.fst) = false by simp_all
        refine Bool.eq_false_iff.2 fun hcon => Bool.false_ne_true ?_
        rw [← h.containsKey_eq_false, containsKey_eq_of_beq hcon,
          containsKey_eq_isSome_findEntry?, hk, Option.isSome_some]
    · cases k == p.fst
      · rw [cond_false]
        exact Or.inr
      · rw [cond_true, Option.some.injEq]
        exact Or.inl ∘ Eq.symm

section
variable {β : Type v}

@[simp] theorem values_nil : ([] : List ((_ : α) × β)).values = [] := rfl
@[simp] theorem values_cons {l : List ((_ : α) × β)} {k : α} {v : β} : (⟨k, v⟩ :: l).values = v :: l.values := rfl

theorem values_eq_map {l : List ((_ : α) × β)} : l.values = l.map (·.2) := by
  induction l using assoc_induction <;> simp_all

theorem mem_values_iff_exists_findValue?_eq_some [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {v : β} (h : l.DistinctKeys) :
    v ∈ l.values ↔ ∃ k, l.findValue? k = some v := by
  simp only [values_eq_map, List.mem_map, mem_iff_findEntry?_eq_some h, findValue?_eq_findEntry?]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, by simp_all⟩
  · rintro ⟨k, hk⟩
    simp only [Option.map_eq_some'] at hk
    rcases hk with ⟨a, ha, rfl⟩
    refine ⟨a, ⟨?_, rfl⟩⟩
    rw [findEntry?_eq_of_beq (findEntry?_eq_some ha), ha]

end

theorem DistinctKeys.replaceEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.DistinctKeys) :
    (l.replaceEntry k v).DistinctKeys := by
  induction l using assoc_induction
  · simp
  · next k' v' l ih =>
    rw [distinctKeys_cons_iff] at h
    cases hk'k : k' == k
    · rw [replaceEntry_cons_of_false hk'k, distinctKeys_cons_iff]
      refine ⟨ih h.1, ?_⟩
      simpa using h.2
    · rw [replaceEntry_cons_of_true hk'k, distinctKeys_cons_iff]
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

theorem DistinctKeys.insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} (h : l.DistinctKeys) : (l.insertEntry k v).DistinctKeys := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', distinctKeys_cons_iff]
    exact ⟨h, h'⟩
  · rw [insertEntry_of_containsKey h']
    exact h.replaceEntry

section

variable {β : Type v}

theorem findValue?_insertEntry_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    (l.insertEntry k v).findValue? a = some v := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', findValue?_cons_of_true h]
  · rw [insertEntry_of_containsKey h', findValue?_replaceEntry_of_true h' (BEq.symm h)]

theorem findValue?_insertEntry_of_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (l.insertEntry k v).findValue? k = some v :=
  findValue?_insertEntry_of_beq BEq.refl

theorem findValue?_insertEntry_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : (k == a) = false) :
    (l.insertEntry k v).findValue? a = l.findValue? a := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', findValue?_cons_of_false h]
  · rw [insertEntry_of_containsKey h', findValue?_replaceEntry_of_false (BEq.symm_false h)]

theorem findValue?_insertEntry [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} :
    (l.insertEntry k v).findValue? a = bif k == a then some v else l.findValue? a := by
  cases h : k == a
  · simp [findValue?_insertEntry_of_false h, h]
  · simp [findValue?_insertEntry_of_beq h, h]

theorem mem_values_insertEntry [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {a : α} {b v : β}
    (h : l.DistinctKeys) : v ∈ (l.insertEntry a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ l.findValue? k = some v := by
  simp only [mem_values_iff_exists_findValue?_eq_some h.insertEntry, findValue?_insertEntry, cond_eq_if]
  refine ⟨?_, ?_⟩
  · simp only [forall_exists_index]
    intro a'
    split
    · rintro ⟨rfl⟩
      exact Or.inl rfl
    · exact fun h => Or.inr ⟨a', ⟨by simp_all, h⟩⟩
  · rintro (rfl|⟨a', h₁, h₂⟩)
    · exact ⟨a, by simp⟩
    · exact ⟨a', by simp_all⟩

@[simp]
theorem mem_values_insertEntry_self [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} {a : α} {b : β} :
    b ∈ (l.insertEntry a b).values := by
  rw [insertEntry]
  cases h : containsKey a l
  · simp
  · simp only [cond_true]
    induction l using assoc_induction
    · simp_all
    · next k v t ih =>
      rw [replaceEntry_cons]
      cases hka : k == a
      · simp only [cond_false, values_cons, mem_cons]
        exact Or.inr (ih (containsKey_of_containsKey_cons h hka))
      · simp

end

-- TODO: Unify order in `bif k == a` vs. `bif a == k`.
theorem findKey?_insertEntry_of_containsKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : l.containsKey k) : (l.insertEntry k v).findKey? a = bif k == a then some k else l.findKey? a := by
  simp [insertEntry_of_containsKey h, findKey?_replaceEntry, h, BEq.comm]

theorem findKey?_insertEntry_of_containsKey_eq_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (hl : (l.containsKey k) = false) :
    (l.insertEntry k v).findKey? a = bif k == a then some k else l.findKey? a := by
  simp [insertEntry_of_containsKey_eq_false hl, findKey?_cons]

theorem findKey?_insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).findKey? a = bif k == a then some k else l.findKey? a := by
  cases hl : l.containsKey k
  · simp [findKey?_insertEntry_of_containsKey_eq_false hl, hl]
  · simp [findKey?_insertEntry_of_containsKey hl]

theorem findEntry?_insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).findEntry? a = bif k == a then some ⟨k, v⟩ else l.findEntry? a := by
  cases hl : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false hl, findEntry?_cons]
  · rw [insertEntry_of_containsKey hl, findEntry?_replaceEntry, hl, Bool.true_and, BEq.comm]

-- TODO: findEntry?_insertEntry_of_beq, findEntry?_insertEntry_of_beq_eq_false

@[simp]
theorem containsKey_insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).containsKey a = ((k == a) || l.containsKey a) := by
  rw [containsKey_eq_isSome_findKey?, containsKey_eq_isSome_findKey?, findKey?_insertEntry]
  cases k == a
  · simp
  · simp

theorem containsKey_insertEntry_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (l.insertEntry k v).containsKey a := by
  simp [h]

@[simp]
theorem containsKey_insertEntry_self [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.insertEntry k v).containsKey k :=
  containsKey_insertEntry_of_beq BEq.refl

@[simp]
theorem keys_eraseKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} :
    (l.eraseKey k).keys = l.keys.erase k := by
  induction l using assoc_induction
  · rfl
  · next k' v' l ih =>
    simp only [eraseKey_cons, keys_cons, List.erase_cons]
    cases k' == k
    · simp [ih]
    · simp [ih]

theorem DistinctKeys.eraseKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} : l.DistinctKeys → (l.eraseKey k).DistinctKeys := by
  apply distinctKeys_of_sublist_keys (by simpa using List.erase_sublist _ _)

theorem findEntry?_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.DistinctKeys) :
    (l.eraseKey k).findEntry? k = none := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [eraseKey_cons_of_false h', findEntry?_cons_of_false h']
      exact ih h.tail
    · rw [eraseKey_cons_of_beq h', ← Option.not_isSome_iff_eq_none, Bool.not_eq_true,
        ← containsKey_eq_isSome_findEntry?, ← containsKey_eq_of_beq h']
      exact h.containsKey_eq_false

theorem findEntry?_eraseKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.eraseKey k).findEntry? a = none := by
  rw [← findEntry?_eq_of_beq hka, findEntry?_eraseKey_self hl]

theorem findEntry?_eraseKey_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α}
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

theorem findEntry?_eraseKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.eraseKey k).findEntry? a = bif k == a then none else l.findEntry? a := by
  cases h : k == a
  · simp [findEntry?_eraseKey_of_false h, h]
  · simp [findEntry?_eraseKey_of_beq hl h, h]

theorem keys_filterMap [BEq α] {l : List (Σ a, β a)} {f : (a : α) → β a → Option (γ a)} :
    (l.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)).keys = (l.filter fun p => (f p.1 p.2).isSome).keys := by
  induction l using assoc_induction
  · simp
  · next k v t ih =>
    simp only [filterMap_cons, filter_cons]
    cases f k v <;> simp [ih]

@[simp]
theorem keys_map [BEq α] {l : List (Σ a, β a)} {f : (a : α) → β a → γ a} :
    (l.map fun p => ⟨p.1, f p.1 p.2⟩).keys = l.keys := by
  induction l using assoc_induction <;> simp_all

theorem DistinctKeys.filterMap [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {f : (a : α) → β a → Option (γ a)} :
    l.DistinctKeys → (l.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)).DistinctKeys := by
  apply distinctKeys_of_sublist_keys
  rw [keys_filterMap, keys_eq_map, keys_eq_map]
  apply Sublist.map
  exact filter_sublist l

theorem DistinctKeys.map [BEq α] {l : List (Σ a, β a)} {f : (a : α) → β a → γ a}
    (h : l.DistinctKeys) : (l.map fun p => ⟨p.1, f p.1 p.2⟩).DistinctKeys :=
  h.of_keys_eq keys_map.symm

section

variable {β : Type v}

-- TODO
theorem findValue?_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k : α} (h : l.DistinctKeys) :
    (l.eraseKey k).findValue? k = none := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey_self h]

theorem findValue?_eraseKey_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.eraseKey k).findValue? a = none := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey_of_beq hl hka]

theorem findValue?_eraseKey_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    (hka : (k == a) = false) : (l.eraseKey k).findValue? a = l.findValue? a := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey_of_false hka]

theorem findValue?_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} (hl : l.DistinctKeys) :
    (l.eraseKey k).findValue? a = bif k == a then none else l.findValue? a := by
  simp [findValue?_eq_findEntry?, findEntry?_eraseKey hl, apply_bif (Option.map _)]

end

theorem findKey?_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.DistinctKeys) :
    (l.eraseKey k).findKey? k = none := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey_self h]

theorem findKey?_eraseKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.eraseKey k).findKey? a = none := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey_of_beq hl hka]

theorem findKey?_eraseKey_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.eraseKey k).findKey? a = l.findKey? a := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey_of_false hka]

theorem findKey?_eraseKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.eraseKey k).findKey? a = bif k == a then none else l.findKey? a := by
  simp [findKey?_eq_findEntry?, findEntry?_eraseKey hl, apply_bif (Option.map _)]

theorem containsKey_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.DistinctKeys) :
    (l.eraseKey k).containsKey k = false := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eraseKey_self h]

theorem containsKey_eraseKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.eraseKey k).containsKey a = false := by
  rw [← containsKey_eq_of_beq hka, containsKey_eraseKey_self hl]

theorem containsKey_eraseKey_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.eraseKey k).containsKey a = l.containsKey a := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eraseKey_of_false hka]

theorem containsKey_eraseKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.eraseKey k).containsKey a = bif k == a then false else l.containsKey a := by
  simp [containsKey_eq_isSome_findEntry?, findEntry?_eraseKey hl, apply_bif Option.isSome]

-- TODO: Technically this should be true without assuming l.DistinctKeys
theorem containsKey_of_containsKey_eraseKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys)
    (h : (l.eraseKey k).containsKey a) : l.containsKey a := by
  cases hka : k == a
  · rwa [containsKey_eraseKey_of_false hka] at h
  · simp [containsKey_eraseKey_of_beq hl hka] at h

theorem findEntry?_of_perm [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} {k : α} (hl : l.DistinctKeys)
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
    simp only [distinctKeys_cons_iff, containsKey_cons, Bool.or_eq_false_iff] at hl
    exact ((Bool.eq_false_iff.1 hl.2.1).elim (BEq.trans h₁ (BEq.symm h₂))).elim
  · next l₁ l₂ l₃ hl₁₂ _ ih₁ ih₂ => exact (ih₁ hl).trans (ih₂ (hl.perm (hl₁₂.symm)))

theorem containsKey_of_perm [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} {k : α} (hl : l.DistinctKeys)
    (h : l ~ l') : l.containsKey k = l'.containsKey k := by
  simp only [containsKey_eq_isSome_findEntry?, findEntry?_of_perm hl h]

theorem findValueCast?_of_perm [BEq α] [LawfulBEq α] {l l' : List (Σ a, β a)} {k : α} (hl : l.DistinctKeys)
    (h : l ~ l') : l.findValueCast? k = l'.findValueCast? k := by
  rw [findValueCast?_eq_findEntry?, findValueCast?_eq_findEntry?, Option.dmap_congr (findEntry?_of_perm hl h)]

section

variable {β : Type v}

theorem findValue?_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((_ : α) × β)} {k : α} (hl : l.DistinctKeys)
    (h : l ~ l') : l.findValue? k = l'.findValue? k := by
  simp only [findValue?_eq_findEntry?, findEntry?_of_perm hl h]

theorem mem_values_of_perm [BEq α] [EquivBEq α] {l l' : List ((_ : α) × β)} {v : β} (hl : l.DistinctKeys)
    (h : l ~ l') : v ∈ l.values ↔ v ∈ l'.values := by
  rw [mem_values_iff_exists_findValue?_eq_some hl, mem_values_iff_exists_findValue?_eq_some (hl.perm h.symm)]
  simp only [findValue?_of_perm hl h]

end

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

-- Note: this theorem becomes false if you don't assume that BEq is reflexive on α.
theorem findEntry?_ext [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} (hl : l.DistinctKeys) (hl' : l'.DistinctKeys)
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
    apply ih hl.tail (hl'.perm hl''.symm).tail
    intro k'
    cases hk' : k' == k
    · simpa only [findEntry?_of_perm hl' hl'', findEntry?_cons_of_false (BEq.symm_false hk')] using h k'
    · simp only [findEntry?_eq_of_beq hk']
      rw [findEntry?_eq_none.2 hl.containsKey_eq_false,
          findEntry?_eq_none.2 (hl'.perm hl''.symm).containsKey_eq_false]

theorem replaceEntry_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} {v : β k}
    (hl : l.DistinctKeys) (h : l ~ l') : l.replaceEntry k v ~ l'.replaceEntry k v := by
  apply findEntry?_ext hl.replaceEntry (hl.perm h.symm).replaceEntry
  simp [findEntry?_replaceEntry, findEntry?_of_perm hl h, containsKey_of_perm hl h]

theorem insertEntry_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} {v : β k}
    (hl : l.DistinctKeys) (h : l ~ l') : l.insertEntry k v ~ l'.insertEntry k v := by
  apply findEntry?_ext hl.insertEntry (hl.perm h.symm).insertEntry
  simp [findEntry?_insertEntry, findEntry?_of_perm hl h]

theorem eraseKey_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α}
    (hl : l.DistinctKeys) (h : l ~ l') : l.eraseKey k ~ l'.eraseKey k := by
  apply findEntry?_ext hl.eraseKey (hl.perm h.symm).eraseKey
  simp [findEntry?_eraseKey hl, findEntry?_eraseKey (hl.perm h.symm), findEntry?_of_perm hl h]

@[simp]
theorem findEntry?_append [BEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').findEntry? k = (l.findEntry? k).or (l'.findEntry? k) := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih => cases h : k' == k <;> simp_all [findEntry?_cons]

theorem findEntry?_append_of_containsKey_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').findEntry? k = l.findEntry? k := by
  rw [findEntry?_append, findEntry?_eq_none.2 h, Option.or_none]

@[simp]
theorem containsKey_append [BEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').containsKey k = (l.containsKey k || l'.containsKey k) := by
  simp [containsKey_eq_isSome_findEntry?]

theorem containsKey_append_of_not_contains_right [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (hl' : l'.containsKey k = false) : (l ++ l').containsKey k = l.containsKey k := by
  simp [hl']

@[simp]
theorem findValue?_append {β : Type v} [BEq α] {l l' : List ((_ : α) × β)} {k : α} :
    (l ++ l').findValue? k = (l.findValue? k).or (l'.findValue? k) := by
  simp [findValue?_eq_findEntry?, Option.map_or]

theorem findValue?_append_of_containsKey_eq_false {β : Type v} [BEq α] {l l' : List ((_ : α) × β)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').findValue? k = l.findValue? k := by
  rw [findValue?_append, findValue?_eq_none.2 h, Option.or_none]

theorem findValueCast?_append_of_containsKey_eq_false [BEq α] [LawfulBEq α] {l l' : List (Σ a, β a)} {k : α}
    (hl' : l'.containsKey k = false) : (l ++ l').findValueCast? k = l.findValueCast? k := by
  rw [findValueCast?_eq_findEntry?, findValueCast?_eq_findEntry?, Option.dmap_congr findEntry?_append,
    Option.dmap_congr (by rw [findEntry?_eq_none.2 hl']), Option.dmap_congr (by rw [Option.or_none])]

@[simp]
theorem findKey?_append [BEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').findKey? k = (l.findKey? k).or (l'.findKey? k) := by
  simp [findKey?_eq_findEntry?, Option.map_or]

theorem findKey?_append_of_containsKey_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').findKey? k = l.findKey? k := by
  rw [findKey?_append, findKey?_eq_none.2 h, Option.or_none]

theorem replaceEntry_append_of_containsKey_left [BEq α] {l l' : List (Σ a, β a)} {k : α}
    {v : β k} (h : l.containsKey k) : (l ++ l').replaceEntry k v = l.replaceEntry k v ++ l' := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_true] at h
    cases h' : k' == k
    · simpa [replaceEntry_cons, h'] using ih (h.resolve_left (Bool.not_eq_true _ ▸ h'))
    · simp [replaceEntry_cons, h']

theorem replaceEntry_append_of_containsKey_left_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    {v : β k} (h : l.containsKey k = false) : (l ++ l').replaceEntry k v = l ++ l'.replaceEntry k v := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_false_iff] at h
    simpa [replaceEntry_cons, h.1] using ih h.2

theorem replaceEntry_append_of_containsKey_right_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    {v : β k} (h : l'.containsKey k = false) : (l ++ l').replaceEntry k v = l.replaceEntry k v ++ l' := by
  cases h' : l.containsKey k
  · rw [replaceEntry_of_containsKey_eq_false, replaceEntry_of_containsKey_eq_false h']
    simpa using ⟨h', h⟩
  · rw [replaceEntry_append_of_containsKey_left h']

theorem insertEntry_append_of_not_contains_right [BEq α] {l l' : List (Σ a, β a)}
    {k : α} {v : β k} (h' : l'.containsKey k = false) :
    (l ++ l').insertEntry k v = l.insertEntry k v ++ l' := by
  cases h : l.containsKey k
  · simp [insertEntry, containsKey_append, h, h']
  · simp [insertEntry, containsKey_append, h, h', replaceEntry_append_of_containsKey_left h]

theorem eraseKey_append_of_containsKey_right_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').eraseKey k = l.eraseKey k ++ l' := by
  induction l using assoc_induction
  · simp [eraseKey_of_containsKey_eq_false h]
  · next k' v' t ih =>
    rw [cons_append, eraseKey_cons, eraseKey_cons]
    cases k' == k
    · rw [cond_false, cond_false, ih, cons_append]
    · rw [cond_true, cond_true]

-- TODO: results about combining modification operations

end List
