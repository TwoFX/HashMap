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
import Hashmap.ForUpstream

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

theorem bif_pos {b : Bool} {a a' : α} (h : b = true) : (bif b then a else a') = a := by
  rw [h, cond_true]

theorem bif_neg {b : Bool} {a a' : α} (h : b = false) : (bif b then a else a') = a' := by
  rw [h, cond_false]

end

namespace List

@[elab_as_elim]
theorem assoc_induction {motive : List (Σ a, β a) → Prop} (nil : motive [])
    (cons : (k : α) → (v : β k) → (tail : List (Σ a, β a)) → motive tail → motive (⟨k, v⟩ :: tail)) :
    (t : List (Σ a, β a)) → motive t
  | [] => nil
  | ⟨_, _⟩ :: _ => cons _ _ _ (assoc_induction nil cons _)

/-- Search for an entry in a list of dependent pairs by key. -/
def getEntry? [BEq α] (a : α) : List (Σ a, β a) → Option (Σ a, β a)
  | [] => none
  | ⟨k, v⟩ :: l => bif k == a then some ⟨k, v⟩ else getEntry? a l

@[simp] theorem getEntry?_nil [BEq α] {a : α} : ([] : List (Σ a, β a)).getEntry? a = none := rfl
theorem getEntry?_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).getEntry? a = bif k == a then some ⟨k, v⟩ else l.getEntry? a := rfl

theorem getEntry?_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).getEntry? a = some ⟨k, v⟩ := by
  simp [getEntry?, h]

theorem getEntry?_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).getEntry? a = l.getEntry? a := by
  simp [getEntry?, h]

@[simp]
theorem getEntry?_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).getEntry? k = some ⟨k, v⟩ :=
  getEntry?_cons_of_true BEq.refl

theorem getEntry?_eq_some [BEq α] {l : List (Σ a, β a)} {a : α} {p : Σ a, β a}
    (h : l.getEntry? a = some p) : p.1 == a := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    cases h' : k' == a
    · rw [getEntry?_cons_of_false h'] at h
      exact ih h
    · rw [getEntry?_cons_of_true h', Option.some.injEq] at h
      obtain rfl := congrArg Sigma.fst h
      exact h'

theorem getEntry?_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.getEntry? a = l.getEntry? a' := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h' : k == a
    · have h₂ : (k == a') = false := BEq.neq_of_neq_of_beq h' h
      rw [getEntry?_cons_of_false h', getEntry?_cons_of_false h₂, ih]
    · rw [getEntry?_cons_of_true h', getEntry?_cons_of_true (BEq.trans h' h)]

theorem isEmpty_eq_false_iff_exists_isSome_getEntry? [BEq α] [ReflBEq α] : {l : List (Σ a, β a)} →
    l.isEmpty = false ↔ ∃ a, (l.getEntry? a).isSome
  | [] => by simp
  | (⟨k, v⟩::l) => by simpa using ⟨k, by simp⟩

section

variable {β : Type v}

def getValue? [BEq α] (a : α) : List ((_ : α) × β) → Option β
  | [] => none
  | ⟨k, v⟩ :: l => bif k == a then some v else l.getValue? a

@[simp] theorem getValue?_nil [BEq α] {a : α} : ([] : List ((_ : α) × β)).getValue? a = none := rfl
theorem getValue?_cons [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} :
    (⟨k, v⟩ :: l).getValue? a = bif k == a then some v else l.getValue? a := rfl

theorem getValue?_cons_of_true [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    (⟨k, v⟩ :: l).getValue? a = some v := by
  simp [getValue?, h]

theorem getValue?_cons_of_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).getValue? a = l.getValue? a := by
  simp [getValue?, h]

@[simp]
theorem getValue?_cons_self [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (⟨k, v⟩ :: l).getValue? k = some v :=
  getValue?_cons_of_true BEq.refl

theorem getValue?_eq_getEntry? [BEq α] {l : List ((_ : α) × β)} {a : α} :
    l.getValue? a = (l.getEntry? a).map (·.2) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [getEntry?_cons_of_false h, getValue?_cons_of_false h, ih]
    · rw [getEntry?_cons_of_true h, getValue?_cons_of_true h, Option.map_some']

theorem getValue?_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {a a' : α} (h : a == a') :
    l.getValue? a = l.getValue? a' := by
  simp [getValue?_eq_getEntry?, getEntry?_eq_of_beq h]

-- TODO
@[simp] theorem Option.isSome_map (α : Type u) (β : Type v) (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by
  cases o <;> simp

theorem isEmpty_eq_false_iff_exists_isSome_getValue? [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} :
    l.isEmpty = false ↔ ∃ a, (l.getValue? a).isSome := by
  simp [isEmpty_eq_false_iff_exists_isSome_getEntry?, getValue?_eq_getEntry?]

end

def getValueCast? [BEq α] [LawfulBEq α] (a : α) : List (Σ a, β a) → Option (β a)
  | [] => none
  | ⟨k, v⟩ :: l => if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else l.getValueCast? a

@[simp] theorem getValueCast?_nil [BEq α] [LawfulBEq α] {a : α} :
    ([] : List (Σ a, β a)).getValueCast? a = none := rfl
theorem getValueCast?_cons [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).getValueCast? a = if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else l.getValueCast? a := rfl

theorem getValueCast?_cons_of_true [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).getValueCast? a = some (cast (congrArg β (eq_of_beq h)) v) := by
  simp [getValueCast?, h]

theorem getValueCast?_cons_of_false [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : (k == a) = false) : (⟨k, v⟩ :: l).getValueCast? a = l.getValueCast? a := by
  simp [getValueCast?, h]

@[simp]
theorem getValueCast?_cons_self [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).getValueCast? k = some v := by
  rw [getValueCast?_cons_of_true BEq.refl, cast_eq]

theorem getValueCast?_eq_getValue? [BEq α] [LawfulBEq α] {β : Type v} {l : List ((_ : α) × β)} {a : α} :
    l.getValueCast? a = l.getValue? a := by
  induction l using assoc_induction <;> simp_all [getValueCast?_cons, getValue?_cons]

def getValueWithCast? [BEq α] (a : α) (cast : ∀ {b}, b == a → β b → β a) : List (Σ a, β a) → Option (β a)
  | [] => none
  | ⟨k, v⟩ :: l => if h : k == a then some (cast h v) else l.getValueWithCast? a cast

@[simp] theorem getValueWithCast?_nil [BEq α] {a : α} {cast : ∀ {b}, b == a → β b → β a} :
    ([] : List (Σ a, β a)).getValueWithCast? a cast = none := rfl
theorem getValueWithCast?_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {cast : ∀ {b}, b == a → β b → β a} :
    (⟨k, v⟩ :: l).getValueWithCast? a cast = if h : k == a then some (cast h v) else l.getValueWithCast? a cast := rfl

theorem getValueWithCast?_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {cast : ∀ {b}, b == a → β b → β a} (h : k == a) :
    (⟨k, v⟩ :: l).getValueWithCast? a cast = some (cast h v) := by
  simp [getValueWithCast?, h]

theorem getValueWithCast?_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {cast : ∀ {b}, b == a → β b → β a}
    (h : (k == a) = false) : (⟨k, v⟩ :: l).getValueWithCast? a cast = l.getValueWithCast? a cast := by
  simp [getValueWithCast?, h]

@[simp]
theorem getValueWithCast?_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} {cast : ∀ {b}, b == k → β b → β k} :
    (⟨k, v⟩ :: l).getValueWithCast? k cast = some (cast BEq.refl v) := by
  rw [getValueWithCast?_cons_of_true BEq.refl]

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

theorem getValueCast?_eq_getEntry? [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a : α} :
    l.getValueCast? a = (l.getEntry? a).dmap (fun p h => cast (congrArg β (eq_of_beq (getEntry?_eq_some h))) p.2) := by
  induction l using assoc_induction
  · simp
  · next k v t ih =>
    cases h : k == a
    · rw [getValueCast?_cons_of_false h, ih, Option.dmap_congr (getEntry?_cons_of_false h)]
    · rw [getValueCast?_cons_of_true h, Option.dmap_congr (getEntry?_cons_of_true h), Option.dmap_some]

theorem isSome_getValueCast?_eq_isSome_getEntry? [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a : α} :
    (l.getValueCast? a).isSome = (l.getEntry? a).isSome := by
  rw [getValueCast?_eq_getEntry?, Option.isSome_dmap]

theorem getValueCast?_congr [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.getValueCast? a = cast (congrArg _ (congrArg _ (eq_of_beq h).symm)) (l.getValueCast? a') := by
  obtain rfl := eq_of_beq h
  rw [cast_eq]

theorem isEmpty_eq_false_iff_exists_isSome_getValueCast? [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} :
    l.isEmpty = false ↔ ∃ a, (l.getValueCast? a).isSome := by
  simp [isEmpty_eq_false_iff_exists_isSome_getEntry?, isSome_getValueCast?_eq_isSome_getEntry?]

def getKey? [BEq α] (a : α) : List (Σ a, β a) → Option α
  | nil => none
  | ⟨k, _⟩ :: l => bif k == a then some k else l.getKey? a

@[simp] theorem getKey?_nil [BEq α] {a : α} : (nil : List (Σ a, β a)).getKey? a = none := rfl
theorem getKey?_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).getKey? a = bif k == a then some k else l.getKey? a := rfl

theorem getKey?_cons_of_true [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).getKey? a = some k := by
  simp [getKey?, h]

theorem getKey?_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).getKey? a = l.getKey? a := by
  simp [getKey?, h]

@[simp]
theorem getKey?_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).getKey? k = k :=
  getKey?_cons_of_true BEq.refl

theorem getKey?_eq_getEntry? [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.getKey? a = (l.getEntry? a).map (·.1) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [getEntry?_cons_of_false h, getKey?_cons_of_false h, ih]
    · rw [getEntry?_cons_of_true h, getKey?_cons_of_true h, Option.map_some']

theorem getKey?_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a a' : α} (h : a == a') :
    l.getKey? a = l.getKey? a' := by
  simp [getKey?_eq_getEntry?, getEntry?_eq_of_beq h]

theorem isEmpty_eq_false_iff_exists_isSome_getKey? [BEq α] [ReflBEq α] {l : List (Σ a, β a)} :
    l.isEmpty = false ↔ ∃ a, (l.getKey? a).isSome := by
  simp [isEmpty_eq_false_iff_exists_isSome_getEntry?, getKey?_eq_getEntry?]

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

theorem containsKey_eq_isSome_getEntry? [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = (l.getEntry? a).isSome := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · simp [getEntry?_cons_of_false h, h, ih]
    · simp [getEntry?_cons_of_true h, h]

theorem isEmpty_eq_false_of_containsKey [BEq α] {l : List (Σ a, β a)} {a : α} (h : l.containsKey a = true) :
    l.isEmpty = false := by
  cases l <;> simp_all

theorem isEmpty_eq_false_iff_exists_containsKey [BEq α] [ReflBEq α] {l : List (Σ a, β a)} :
    l.isEmpty = false ↔ ∃ a, l.containsKey a := by
  simp [isEmpty_eq_false_iff_exists_isSome_getEntry?, containsKey_eq_isSome_getEntry?]

@[simp]
theorem getEntry?_eq_none [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.getEntry? a = none ↔ l.containsKey a = false := by
  rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, ← containsKey_eq_isSome_getEntry?]

@[simp]
theorem getKey?_eq_none [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.getKey? a = none ↔ l.containsKey a = false := by
  rw [getKey?_eq_getEntry?, Option.map_eq_none', getEntry?_eq_none]

@[simp]
theorem getValue?_eq_none {β : Type v} [BEq α] {l : List ((_ : α) × β)} {a : α} :
    l.getValue? a = none ↔ l.containsKey a = false := by
  rw [getValue?_eq_getEntry?, Option.map_eq_none', getEntry?_eq_none]

theorem containsKey_eq_isSome_getValue? {β : Type v} [BEq α] {l : List ((_ : α) × β)} {a : α} :
    l.containsKey a = (l.getValue? a).isSome := by
  simp [containsKey_eq_isSome_getEntry?, getValue?_eq_getEntry?]

theorem containsKey_eq_isSome_getKey? [BEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = (l.getKey? a).isSome := by
  simp [containsKey_eq_isSome_getEntry?, getKey?_eq_getEntry?]

theorem containsKey_eq_isSome_getValueCast? [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a : α} :
    l.containsKey a = (l.getValueCast? a).isSome := by
  simp [containsKey_eq_isSome_getEntry?, getValueCast?_eq_getEntry?]

theorem containsKey_eq_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a b : α} (h : a == b) :
    l.containsKey a = l.containsKey b := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_eq_of_beq h]

theorem containsKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {a b : α} (hla : l.containsKey a) (hab : a == b) :
    l.containsKey b := by
  rwa [← containsKey_eq_of_beq hab]

def getEntry [BEq α] (l : List (Σ a, β a)) (a : α) (h : l.containsKey a) : Σ a, β a :=
  (l.getEntry? a).get <| containsKey_eq_isSome_getEntry?.symm.trans h

theorem getEntry?_eq_some_getEntry [BEq α] {l : List (Σ a, β a)} {a : α} (h : l.containsKey a) :
    l.getEntry? a = some (l.getEntry a h) := by
  simp [getEntry]

theorem getEntry_eq_of_getEntry?_eq_some [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : l.getEntry? a = some ⟨k, v⟩) {h'} : l.getEntry a h' = ⟨k, v⟩ := by
  simp [getEntry, h]

theorem getEntry_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).getEntry a (containsKey_cons_of_beq (v := v) h) = ⟨k, v⟩ := by
  simp [getEntry, getEntry?_cons_of_true h]

@[simp]
theorem getEntry_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).getEntry k containsKey_cons_self = ⟨k, v⟩ :=
  getEntry_cons_of_beq BEq.refl

theorem getEntry_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {h₁ : (⟨k, v⟩ :: l).containsKey a}
    (h₂ : (k == a) = false) :
    (⟨k, v⟩ :: l).getEntry a h₁ = l.getEntry a (containsKey_of_containsKey_cons (v := v) h₁ h₂) := by
  simp [getEntry, getEntry?_cons_of_false h₂]

def getKey [BEq α] (l : List (Σ a, β a)) (a : α) (h : l.containsKey a) : α :=
  (l.getKey? a).get <| containsKey_eq_isSome_getKey?.symm.trans h

theorem getKey?_eq_some_getKey [BEq α] {l : List (Σ a, β a)} {a : α} (h : l.containsKey a) :
    l.getKey? a = some (l.getKey a h) := by
  simp [getKey]

theorem getKey_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).getKey a (containsKey_cons_of_beq (v := v) h) = k := by
  simp [getKey, getKey?_cons_of_true h]

@[simp]
theorem getKey_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).getKey k containsKey_cons_self = k :=
  getKey_cons_of_beq BEq.refl

theorem getKey_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {h₁ : (⟨k, v⟩ :: l).containsKey a}
    (h₂ : (k == a) = false) : (⟨k, v⟩ :: l).getKey a h₁ = l.getKey a (containsKey_of_containsKey_cons (v := v) h₁ h₂) := by
  simp [getKey, getKey?_cons_of_false h₂]

theorem getKey_beq [BEq α] {l : List (Σ a, β a)} {a : α} {h : l.containsKey a} : l.getKey a h == a := by
  induction l using assoc_induction
  · simp at h
  · next k v t ih =>
    cases h' : k == a
    · rw [getKey_cons_of_false h']
      exact @ih (containsKey_of_containsKey_cons h h')
    · rwa [getKey_cons_of_beq h']

section

variable {β : Type v}

def getValue [BEq α] (a : α) (l : List ((_ : α) × β)) (h : l.containsKey a) : β :=
  (l.getValue? a).get <| containsKey_eq_isSome_getValue?.symm.trans h

theorem getValue?_eq_some_getValue [BEq α] {l : List ((_ : α) × β)} {a : α} (h : l.containsKey a) :
    l.getValue? a = some (l.getValue a h) := by
  simp [getValue]

theorem getValue_cons_of_beq [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    (⟨k, v⟩ :: l).getValue a (containsKey_cons_of_beq (k := k) (v := v) h) = v := by
  simp [getValue, getValue?_cons_of_true h]

@[simp]
theorem getValue_cons_self [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (⟨k, v⟩ :: l).getValue k containsKey_cons_self = v :=
  getValue_cons_of_beq BEq.refl

theorem getValue_cons_of_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} {h₁ : (⟨k, v⟩ :: l).containsKey a}
    (h₂ : (k == a) = false) : (⟨k, v⟩ :: l).getValue a h₁ = l.getValue a (containsKey_of_containsKey_cons (k := k) (v := v) h₁ h₂) := by
  simp [getValue, getValue?_cons_of_false h₂]

theorem getValue_cons [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} {h} :
    (⟨k, v⟩ :: l).getValue a h = if h' : k == a then v else l.getValue a (containsKey_of_containsKey_cons (k := k) h (Bool.eq_false_iff.2 h')) := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, getValue?_cons, apply_dite Option.some, cond_eq_if]
  split
  · rfl
  · exact getValue?_eq_some_getValue _

end

def getValueCast [BEq α] [LawfulBEq α] (a : α) (l : List (Σ a, β a)) (h : l.containsKey a) : β a :=
  (l.getValueCast? a).get <| containsKey_eq_isSome_getValueCast?.symm.trans h

theorem getValueCast?_eq_some_getValueCast [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {a : α} (h : l.containsKey a) :
    l.getValueCast? a = some (l.getValueCast a h) := by
  simp [getValueCast]

theorem Option.get_congr {o o' : Option α} {ho : o.isSome} (h : o = o') : o.get ho = o'.get (h ▸ ho) := by
  cases h; rfl

theorem getValueCast_cons [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : (⟨k, v⟩ :: l).containsKey a) :
    (⟨k, v⟩ :: l).getValueCast a h =
      if h' : k == a then
        cast (congrArg β (eq_of_beq h')) v
      else
        l.getValueCast a (containsKey_of_containsKey_cons (k := k) h (Bool.eq_false_iff.2 h')) := by
  rw [getValueCast, Option.get_congr getValueCast?_cons]
  split <;> simp [getValueCast]

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

@[simp]
theorem isEmpty_replaceEntry [BEq α] {l : List (Σ a, β a)} {a : α} {b : β a} : (l.replaceEntry a b).isEmpty = l.isEmpty := by
  induction l using assoc_induction
  · simp
  · simp [replaceEntry_cons, cond_eq_if]
    split <;> simp

theorem getEntry?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).getEntry? k = l.getEntry? k := by
  rw [replaceEntry_of_containsKey_eq_false hl]

theorem getEntry?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replaceEntry a b).getEntry? k = l.getEntry? k := by
  induction l using assoc_induction
  · simp
  · next k' v' l ih =>
    cases h' : k' == a
    · rw [replaceEntry_cons_of_false h', getEntry?_cons, getEntry?_cons, ih]
    · rw [replaceEntry_cons_of_true h']
      have hk : (k' == k) = false := BEq.neq_of_beq_of_neq h' (BEq.symm_false h)
      simp [getEntry?_cons_of_false (BEq.symm_false h), getEntry?_cons_of_false hk]

theorem getEntry?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} (hl : l.containsKey a = true)
    (h : k == a) : (l.replaceEntry a b).getEntry? k = some ⟨a, b⟩ := by
  induction l using assoc_induction
  · simp at hl
  · next k' v' l ih =>
    cases hk'a : k' == a
    · rw [replaceEntry_cons_of_false hk'a]
      have hk'k : (k' == k) = false := BEq.neq_of_neq_of_beq hk'a (BEq.symm h)
      rw [getEntry?_cons_of_false hk'k]
      exact ih (containsKey_of_containsKey_cons hl hk'a)
    · rw [replaceEntry_cons_of_true hk'a, getEntry?_cons_of_true (BEq.symm h)]

theorem getEntry?_replaceEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).getEntry? k = bif l.containsKey a && k == a then some ⟨a, b⟩ else
      l.getEntry? k := by
  cases hl : l.containsKey a
  · simp [getEntry?_replaceEntry_of_containsKey_eq_false hl]
  · cases h : k == a
    · simp [getEntry?_replaceEntry_of_false h]
    · simp [getEntry?_replaceEntry_of_true hl h]

@[simp]
theorem length_replaceEntry [BEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.replaceEntry k v).length = l.length := by
  induction l using assoc_induction <;> simp_all [replaceEntry_cons, apply_bif List.length]

section

variable {β : Type v}

theorem getValue?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).getValue? k = l.getValue? k := by
  simp [getValue?_eq_getEntry?, getEntry?_replaceEntry_of_containsKey_eq_false hl]

theorem getValue?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (h : (k == a) = false) : (l.replaceEntry a b).getValue? k = l.getValue? k := by
  simp [getValue?_eq_getEntry?, getEntry?_replaceEntry_of_false h]

theorem getValue?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {b : β}
    (hl : l.containsKey a = true) (h : k == a) : (l.replaceEntry a b).getValue? k = some b := by
  simp [getValue?_eq_getEntry?, getEntry?_replaceEntry_of_true hl h]

end

theorem getValueCast?_replaceEntry [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).getValueCast? k =
      if h : l.containsKey a ∧ a == k then some (cast (congrArg β (eq_of_beq h.2)) b) else l.getValueCast? k := by
  rw [getValueCast?_eq_getEntry?]
  split
  · next h =>
    rw [Option.dmap_congr (getEntry?_replaceEntry_of_true h.1 (BEq.symm h.2)), Option.dmap_some]
  · next h =>
    simp only [Classical.not_and_iff_or_not_not] at h
    rcases h with h|h
    · rw [Option.dmap_congr (getEntry?_replaceEntry_of_containsKey_eq_false (Bool.eq_false_iff.2 h)),
        getValueCast?_eq_getEntry?]
    · rw [Option.dmap_congr (getEntry?_replaceEntry_of_false (BEq.symm_false <| Bool.eq_false_iff.2 h)),
        getValueCast?_eq_getEntry?]

theorem getKey?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = false) : (l.replaceEntry a b).getKey? k = l.getKey? k := by
  simp [getKey?_eq_getEntry?, getEntry?_replaceEntry_of_containsKey_eq_false hl]

theorem getKey?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (h : (k == a) = false) : (l.replaceEntry a b).getKey? k = l.getKey? k := by
  simp [getKey?_eq_getEntry?, getEntry?_replaceEntry_of_false h]

theorem getKey?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a}
    (hl : l.containsKey a = true) (h : (k == a)) : (l.replaceEntry a b).getKey? k = some a := by
  simp [getKey?_eq_getEntry?, getEntry?_replaceEntry_of_true hl h]

theorem getKey?_replaceEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).getKey? k = bif l.containsKey a && k == a then some a else l.getKey? k := by
  cases hl : l.containsKey a
  · simp [getKey?_replaceEntry_of_containsKey_eq_false hl]
  · cases h : k == a
    · simp [getKey?_replaceEntry_of_false h]
    · simp [getKey?_replaceEntry_of_true hl h]

@[simp]
theorem containsKey_replaceEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {b : β a} :
    (l.replaceEntry a b).containsKey k = l.containsKey k := by
  cases h : l.containsKey a && k == a
  · rw [containsKey_eq_isSome_getKey?, getKey?_replaceEntry, h, cond_false, containsKey_eq_isSome_getKey?]
  · rw [containsKey_eq_isSome_getKey?, getKey?_replaceEntry, h, cond_true, Option.isSome_some, Eq.comm]
    rw [Bool.and_eq_true] at h
    exact containsKey_of_beq h.1 (BEq.symm h.2)

def removeKey [BEq α] (a : α) : List (Σ a, β a) → List (Σ a, β a)
  | nil => nil
  | ⟨k, v⟩ :: l => bif k == a then l else ⟨k, v⟩ :: l.removeKey a

@[simp] theorem removeKey_nil [BEq α] {a : α} : (nil : List (Σ a, β a)).removeKey a = nil := rfl
theorem removeKey_cons [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (⟨k, v⟩ :: l).removeKey a = bif k == a then l else ⟨k, v⟩ :: l.removeKey a := rfl

theorem removeKey_cons_of_beq [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : k == a) :
    (⟨k, v⟩ :: l).removeKey a = l :=
  by simp [removeKey_cons, h]

@[simp]
theorem removeKey_cons_self [BEq α] [ReflBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (⟨k, v⟩ :: l).removeKey k = l :=
  removeKey_cons_of_beq BEq.refl

theorem removeKey_cons_of_false [BEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} (h : (k == a) = false) :
    (⟨k, v⟩ :: l).removeKey a = ⟨k, v⟩ :: l.removeKey a := by
  simp [removeKey_cons, h]

theorem removeKey_of_containsKey_eq_false [BEq α] {l : List (Σ a, β a)} {k : α} (h : l.containsKey k = false) :
    l.removeKey k = l := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_false_iff] at h
    rw [removeKey_cons_of_false h.1, ih h.2]

theorem sublist_removeKey [BEq α] {l : List (Σ a, β a)} {k : α} : (l.removeKey k).Sublist l := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    rw [removeKey_cons]
    cases k' == k
    · simpa
    · simp

theorem length_removeKey [BEq α] {l : List (Σ a, β a)} {k : α} :
    (l.removeKey k).length = bif l.containsKey k then l.length - 1 else l.length := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    rw [removeKey_cons, containsKey_cons]
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

theorem length_removeKey_le [BEq α] {l : List (Σ a, β a)} {k : α} :
    (l.removeKey k).length ≤ l.length := by
  rw [length_removeKey]
  cases l.containsKey k
  · simp
  · simpa using Nat.sub_le ..

theorem isEmpty_removeKey [BEq α] {l : List (Σ a, β a)} {k : α} :
    (l.removeKey k).isEmpty = (l.isEmpty || (l.length == 1 && l.containsKey k)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rw [isEmpty_iff_length_eq_zero, length_removeKey, isEmpty_iff_length_eq_zero]
  cases containsKey k l <;> cases l <;> simp

-- TODO: removeKey+replaceEntry

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

theorem mem_iff_getEntry?_eq_some [BEq α] [EquivBEq α] {l : List (Σ a, β a)} {p : Σ a, β a} (h : l.DistinctKeys) :
    p ∈ l ↔ l.getEntry? p.1 = some p := by
  induction l using assoc_induction
  · simp_all
  · next k v t ih =>
    simp only [mem_cons, getEntry?_cons, ih h.tail]
    refine ⟨?_, ?_⟩
    · rintro (rfl|hk)
      · simp
      · suffices (k == p.fst) = false by simp_all
        refine Bool.eq_false_iff.2 fun hcon => Bool.false_ne_true ?_
        rw [← h.containsKey_eq_false, containsKey_eq_of_beq hcon,
          containsKey_eq_isSome_getEntry?, hk, Option.isSome_some]
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

theorem mem_values_iff_exists_getValue?_eq_some [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {v : β} (h : l.DistinctKeys) :
    v ∈ l.values ↔ ∃ k, l.getValue? k = some v := by
  simp only [values_eq_map, List.mem_map, mem_iff_getEntry?_eq_some h, getValue?_eq_getEntry?]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, by simp_all⟩
  · rintro ⟨k, hk⟩
    simp only [Option.map_eq_some'] at hk
    rcases hk with ⟨a, ha, rfl⟩
    refine ⟨a, ⟨?_, rfl⟩⟩
    rw [getEntry?_eq_of_beq (getEntry?_eq_some ha), ha]

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

@[simp]
theorem isEmpty_insertEntry [BEq α] {l : List (Σ a, β a)} {k : α} {v : β k} : (l.insertEntry k v).isEmpty = false := by
  cases h : l.containsKey k
  · simp [insertEntry_of_containsKey_eq_false h]
  · rw [insertEntry_of_containsKey h, isEmpty_replaceEntry, isEmpty_eq_false_of_containsKey h]

theorem length_insertEntry [BEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.insertEntry k v).length = bif l.containsKey k then l.length else l.length + 1 := by
  simp [insertEntry, apply_bif length]

theorem length_le_length_insert [BEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    l.length ≤ (l.insertEntry k v).length := by
  rw [length_insertEntry]
  cases l.containsKey k
  · simpa using Nat.le_add_right ..
  · simp

section

variable {β : Type v}

theorem getValue?_insertEntry_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    (l.insertEntry k v).getValue? a = some v := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', getValue?_cons_of_true h]
  · rw [insertEntry_of_containsKey h', getValue?_replaceEntry_of_true h' (BEq.symm h)]

theorem getValue?_insertEntry_of_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (l.insertEntry k v).getValue? k = some v :=
  getValue?_insertEntry_of_beq BEq.refl

theorem getValue?_insertEntry_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : (k == a) = false) :
    (l.insertEntry k v).getValue? a = l.getValue? a := by
  cases h' : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false h', getValue?_cons_of_false h]
  · rw [insertEntry_of_containsKey h', getValue?_replaceEntry_of_false (BEq.symm_false h)]

theorem getValue?_insertEntry [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} :
    (l.insertEntry k v).getValue? a = bif k == a then some v else l.getValue? a := by
  cases h : k == a
  · simp [getValue?_insertEntry_of_false h, h]
  · simp [getValue?_insertEntry_of_beq h, h]

theorem getValue?_insertEntry_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    (l.insertEntry k v).getValue? k = some v := by
  rw [getValue?_insertEntry, bif_pos BEq.refl]

theorem mem_values_insertEntry [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {a : α} {b v : β}
    (h : l.DistinctKeys) : v ∈ (l.insertEntry a b).values ↔ b = v ∨ ∃ k, (a == k) = false ∧ l.getValue? k = some v := by
  simp only [mem_values_iff_exists_getValue?_eq_some h.insertEntry, getValue?_insertEntry, cond_eq_if]
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
theorem getKey?_insertEntry_of_containsKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h : l.containsKey k) : (l.insertEntry k v).getKey? a = bif k == a then some k else l.getKey? a := by
  simp [insertEntry_of_containsKey h, getKey?_replaceEntry, h, BEq.comm]

theorem getKey?_insertEntry_of_containsKey_eq_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (hl : (l.containsKey k) = false) :
    (l.insertEntry k v).getKey? a = bif k == a then some k else l.getKey? a := by
  simp [insertEntry_of_containsKey_eq_false hl, getKey?_cons]

theorem getKey?_insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).getKey? a = bif k == a then some k else l.getKey? a := by
  cases hl : l.containsKey k
  · simp [getKey?_insertEntry_of_containsKey_eq_false hl, hl]
  · simp [getKey?_insertEntry_of_containsKey hl]

theorem getEntry?_insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).getEntry? a = bif k == a then some ⟨k, v⟩ else l.getEntry? a := by
  cases hl : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false hl, getEntry?_cons]
  · rw [insertEntry_of_containsKey hl, getEntry?_replaceEntry, hl, Bool.true_and, BEq.comm]

theorem getValueCast?_insertEntry [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).getValueCast? a = if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else l.getValueCast? a := by
  cases hl : l.containsKey k
  · rw [insertEntry_of_containsKey_eq_false hl, getValueCast?_cons]
  · rw [insertEntry_of_containsKey hl, getValueCast?_replaceEntry, hl]
    split <;> simp_all

theorem getValueCast?_insertEntry_self [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.insertEntry k v).getValueCast? k = some v := by
  rw [getValueCast?_insertEntry, dif_pos BEq.refl, cast_eq]

-- TODO: getEntry?_insertEntry_of_beq, getEntry?_insertEntry_of_beq_eq_false

@[simp]
theorem containsKey_insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} :
    (l.insertEntry k v).containsKey a = ((k == a) || l.containsKey a) := by
  rw [containsKey_eq_isSome_getKey?, containsKey_eq_isSome_getKey?, getKey?_insertEntry]
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

theorem containsKey_of_containsKey_insertEntry [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k}
    (h₁ : (l.insertEntry k v).containsKey a) (h₂ : (k == a) = false) : l.containsKey a := by
  rwa [containsKey_insertEntry, h₂, Bool.false_or] at h₁

theorem getValueCast_insertEntry [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} {v : β k} {h} :
    (l.insertEntry k v).getValueCast a h =
    if h' : k == a then
      cast (congrArg β (eq_of_beq h')) v
    else
      l.getValueCast a (containsKey_of_containsKey_insertEntry h (Bool.eq_false_iff.2 h')) := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, apply_dite Option.some, getValueCast?_insertEntry]
  simp only [← getValueCast?_eq_some_getValueCast]

theorem getValueCast_insertEntry_self [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k : α} {v : β k} :
    (l.insertEntry k v).getValueCast k containsKey_insertEntry_self = v := by
  simp [getValueCast_insertEntry]

@[simp]
theorem keys_removeKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} :
    (l.removeKey k).keys = l.keys.erase k := by
  induction l using assoc_induction
  · rfl
  · next k' v' l ih =>
    simp only [removeKey_cons, keys_cons, List.erase_cons]
    cases k' == k
    · simp [ih]
    · simp [ih]

theorem DistinctKeys.removeKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} : l.DistinctKeys → (l.removeKey k).DistinctKeys := by
  apply distinctKeys_of_sublist_keys (by simpa using List.erase_sublist _ _)

theorem getEntry?_removeKey_self [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.DistinctKeys) :
    (l.removeKey k).getEntry? k = none := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [removeKey_cons_of_false h', getEntry?_cons_of_false h']
      exact ih h.tail
    · rw [removeKey_cons_of_beq h', ← Option.not_isSome_iff_eq_none, Bool.not_eq_true,
        ← containsKey_eq_isSome_getEntry?, ← containsKey_eq_of_beq h']
      exact h.containsKey_eq_false

theorem getEntry?_removeKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.removeKey k).getEntry? a = none := by
  rw [← getEntry?_eq_of_beq hka, getEntry?_removeKey_self hl]

theorem getEntry?_removeKey_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.removeKey k).getEntry? a = l.getEntry? a := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [removeKey_cons_of_false h']
      cases h'' : k' == a
      · rw [getEntry?_cons_of_false h'', ih, getEntry?_cons_of_false h'']
      · rw [getEntry?_cons_of_true h'', getEntry?_cons_of_true h'']
    · rw [removeKey_cons_of_beq h']
      have hx : (k' == a) = false := BEq.neq_of_beq_of_neq h' hka
      rw [getEntry?_cons_of_false hx]

theorem getEntry?_removeKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.removeKey k).getEntry? a = bif k == a then none else l.getEntry? a := by
  cases h : k == a
  · simp [getEntry?_removeKey_of_false h, h]
  · simp [getEntry?_removeKey_of_beq hl h, h]

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
theorem getValue?_removeKey_self [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k : α} (h : l.DistinctKeys) :
    (l.removeKey k).getValue? k = none := by
  simp [getValue?_eq_getEntry?, getEntry?_removeKey_self h]

theorem getValue?_removeKey_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.removeKey k).getValue? a = none := by
  simp [getValue?_eq_getEntry?, getEntry?_removeKey_of_beq hl hka]

theorem getValue?_removeKey_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    (hka : (k == a) = false) : (l.removeKey k).getValue? a = l.getValue? a := by
  simp [getValue?_eq_getEntry?, getEntry?_removeKey_of_false hka]

theorem getValue?_removeKey [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α} (hl : l.DistinctKeys) :
    (l.removeKey k).getValue? a = bif k == a then none else l.getValue? a := by
  simp [getValue?_eq_getEntry?, getEntry?_removeKey hl, apply_bif (Option.map _)]

end

theorem getKey?_removeKey_self [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.DistinctKeys) :
    (l.removeKey k).getKey? k = none := by
  simp [getKey?_eq_getEntry?, getEntry?_removeKey_self h]

theorem getKey?_removeKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.removeKey k).getKey? a = none := by
  simp [getKey?_eq_getEntry?, getEntry?_removeKey_of_beq hl hka]

theorem getKey?_removeKey_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.removeKey k).getKey? a = l.getKey? a := by
  simp [getKey?_eq_getEntry?, getEntry?_removeKey_of_false hka]

theorem getKey?_removeKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.removeKey k).getKey? a = bif k == a then none else l.getKey? a := by
  simp [getKey?_eq_getEntry?, getEntry?_removeKey hl, apply_bif (Option.map _)]

theorem containsKey_removeKey_self [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k : α} (h : l.DistinctKeys) :
    (l.removeKey k).containsKey k = false := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_removeKey_self h]

theorem containsKey_removeKey_of_beq [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys)
    (hka : k == a) : (l.removeKey k).containsKey a = false := by
  rw [← containsKey_eq_of_beq hka, containsKey_removeKey_self hl]

theorem containsKey_removeKey_of_false [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α}
    (hka : (k == a) = false) : (l.removeKey k).containsKey a = l.containsKey a := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_removeKey_of_false hka]

theorem containsKey_removeKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.removeKey k).containsKey a = (!(k == a) && l.containsKey a) := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_removeKey hl, apply_bif]

theorem getValueCast?_removeKey [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.removeKey k).getValueCast? a = bif k == a then none else l.getValueCast? a := by
  rw [getValueCast?_eq_getEntry?, Option.dmap_congr (getEntry?_removeKey hl)]
  rcases Bool.eq_false_or_eq_true (k == a) with h|h
  · rw [Option.dmap_congr (bif_pos h), Option.dmap_none, bif_pos h]
  · rw [Option.dmap_congr (bif_neg h), getValueCast?_eq_getEntry?]
    exact (bif_neg h).symm

theorem getValueCast?_removeKey_self [BEq α] [LawfulBEq α] {l : List (Σ a, β a)} {k : α} (hl : l.DistinctKeys) :
    (l.removeKey k).getValueCast? k = none := by
  rw [getValueCast?_removeKey hl, bif_pos BEq.refl]

-- TODO: Technically this should be true without assuming l.DistinctKeys
theorem containsKey_of_containsKey_removeKey [BEq α] [PartialEquivBEq α] {l : List (Σ a, β a)} {k a : α} (hl : l.DistinctKeys) :
    (l.removeKey k).containsKey a → l.containsKey a := by
  simp [containsKey_removeKey hl]

theorem getEntry?_of_perm [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} {k : α} (hl : l.DistinctKeys)
    (h : l ~ l') : l.getEntry? k = l'.getEntry? k := by
  induction h
  · simp
  · next p t₁ t₂ _ ih₂ =>
    rcases p with ⟨k', v'⟩
    simp only [getEntry?_cons, ih₂ hl.tail]
  · next p p' t =>
    rcases p with ⟨k₁, v₁⟩
    rcases p' with ⟨k₂, v₂⟩
    simp only [getEntry?_cons]
    cases h₂ : k₂ == k <;> cases h₁ : k₁ == k <;> try simp; done
    simp only [distinctKeys_cons_iff, containsKey_cons, Bool.or_eq_false_iff] at hl
    exact ((Bool.eq_false_iff.1 hl.2.1).elim (BEq.trans h₁ (BEq.symm h₂))).elim
  · next l₁ l₂ l₃ hl₁₂ _ ih₁ ih₂ => exact (ih₁ hl).trans (ih₂ (hl.perm (hl₁₂.symm)))

theorem containsKey_of_perm [BEq α] [PartialEquivBEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l ~ l') : l.containsKey k = l'.containsKey k := by
  induction h
  · simp
  · next p t₁ t₂ _ ih₂ => rw [containsKey_cons, containsKey_cons, ih₂]
  · next p p' t =>
    rw [containsKey_cons, containsKey_cons, containsKey_cons, containsKey_cons]
    ac_rfl
  · next _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem getValueCast?_of_perm [BEq α] [LawfulBEq α] {l l' : List (Σ a, β a)} {k : α} (hl : l.DistinctKeys)
    (h : l ~ l') : l.getValueCast? k = l'.getValueCast? k := by
  rw [getValueCast?_eq_getEntry?, getValueCast?_eq_getEntry?, Option.dmap_congr (getEntry?_of_perm hl h)]

theorem getValueCast_of_perm [BEq α] [LawfulBEq α] {l l' : List (Σ a, β a)} {k : α} {h'} (hl : l.DistinctKeys)
    (h : l ~ l') : l.getValueCast k h' = l'.getValueCast k ((containsKey_of_perm h).symm.trans h') := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, ← getValueCast?_eq_some_getValueCast,
    getValueCast?_of_perm hl h]

section

variable {β : Type v}

theorem getValue?_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((_ : α) × β)} {k : α} (hl : l.DistinctKeys)
    (h : l ~ l') : l.getValue? k = l'.getValue? k := by
  simp only [getValue?_eq_getEntry?, getEntry?_of_perm hl h]

theorem getValue_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((_ : α) × β)} {k : α} {h'} (hl : l.DistinctKeys)
    (h : l ~ l') : l.getValue k h' = l'.getValue k ((containsKey_of_perm h).symm.trans h') := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, ← getValue?_eq_some_getValue, getValue?_of_perm hl h]

theorem mem_values_of_perm [BEq α] [EquivBEq α] {l l' : List ((_ : α) × β)} {v : β} (hl : l.DistinctKeys)
    (h : l ~ l') : v ∈ l.values ↔ v ∈ l'.values := by
  rw [mem_values_iff_exists_getValue?_eq_some hl, mem_values_iff_exists_getValue?_eq_some (hl.perm h.symm)]
  simp only [getValue?_of_perm hl h]

end

theorem perm_cons_getEntry [BEq α] {l : List (Σ a, β a)} {k : α} (h : l.containsKey k) :
    ∃ l', l ~ l.getEntry k h :: l' := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_true] at h
    cases hk : k' == k
    · obtain ⟨l', hl'⟩ := ih (h.resolve_left (Bool.not_eq_true _ ▸ hk))
      rw [getEntry_cons_of_false hk]
      exact ⟨⟨k', v'⟩ :: l', (hl'.cons _).trans (Perm.swap _ _ _)⟩
    · exact ⟨t, by rw [getEntry_cons_of_beq hk]⟩

-- Note: this theorem becomes false if you don't assume that BEq is reflexive on α.
theorem getEntry?_ext [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} (hl : l.DistinctKeys) (hl' : l'.DistinctKeys)
    (h : ∀ k, l.getEntry? k = l'.getEntry? k) : l ~ l' := by
  induction l using assoc_induction generalizing l'
  · induction l' using assoc_induction
    · rfl
    · next k _ _ _ => simpa using h k
  · next k v t ih =>
    have hl'k₁ : l'.getEntry? k = some ⟨k, v⟩ := by rw [← h, getEntry?_cons_self]
    have hl'k₂ : l'.containsKey k := by
      rw [containsKey_eq_isSome_getEntry?, hl'k₁, Option.isSome_some]
    obtain ⟨l'', hl''⟩ := perm_cons_getEntry hl'k₂
    rw [getEntry_eq_of_getEntry?_eq_some hl'k₁] at hl''
    suffices t ~ l'' from (this.cons _).trans hl''.symm
    apply ih hl.tail (hl'.perm hl''.symm).tail
    intro k'
    cases hk' : k' == k
    · simpa only [getEntry?_of_perm hl' hl'', getEntry?_cons_of_false (BEq.symm_false hk')] using h k'
    · simp only [getEntry?_eq_of_beq hk']
      rw [getEntry?_eq_none.2 hl.containsKey_eq_false,
          getEntry?_eq_none.2 (hl'.perm hl''.symm).containsKey_eq_false]

theorem replaceEntry_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} {v : β k}
    (hl : l.DistinctKeys) (h : l ~ l') : l.replaceEntry k v ~ l'.replaceEntry k v := by
  apply getEntry?_ext hl.replaceEntry (hl.perm h.symm).replaceEntry
  simp [getEntry?_replaceEntry, getEntry?_of_perm hl h, containsKey_of_perm h]

theorem insertEntry_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α} {v : β k}
    (hl : l.DistinctKeys) (h : l ~ l') : l.insertEntry k v ~ l'.insertEntry k v := by
  apply getEntry?_ext hl.insertEntry (hl.perm h.symm).insertEntry
  simp [getEntry?_insertEntry, getEntry?_of_perm hl h]

theorem removeKey_of_perm [BEq α] [EquivBEq α] {l l' : List (Σ a, β a)} {k : α}
    (hl : l.DistinctKeys) (h : l ~ l') : l.removeKey k ~ l'.removeKey k := by
  apply getEntry?_ext hl.removeKey (hl.perm h.symm).removeKey
  simp [getEntry?_removeKey hl, getEntry?_removeKey (hl.perm h.symm), getEntry?_of_perm hl h]

@[simp]
theorem getEntry?_append [BEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').getEntry? k = (l.getEntry? k).or (l'.getEntry? k) := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih => cases h : k' == k <;> simp_all [getEntry?_cons]

theorem getEntry?_append_of_containsKey_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').getEntry? k = l.getEntry? k := by
  rw [getEntry?_append, getEntry?_eq_none.2 h, Option.or_none]

@[simp]
theorem containsKey_append [BEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').containsKey k = (l.containsKey k || l'.containsKey k) := by
  simp [containsKey_eq_isSome_getEntry?]

theorem containsKey_append_of_not_contains_right [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (hl' : l'.containsKey k = false) : (l ++ l').containsKey k = l.containsKey k := by
  simp [hl']

@[simp]
theorem getValue?_append {β : Type v} [BEq α] {l l' : List ((_ : α) × β)} {k : α} :
    (l ++ l').getValue? k = (l.getValue? k).or (l'.getValue? k) := by
  simp [getValue?_eq_getEntry?, Option.map_or]

theorem getValue?_append_of_containsKey_eq_false {β : Type v} [BEq α] {l l' : List ((_ : α) × β)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').getValue? k = l.getValue? k := by
  rw [getValue?_append, getValue?_eq_none.2 h, Option.or_none]

theorem getValue_append_of_containsKey_eq_false {β : Type v} [BEq α] {l l' : List ((_ : α) × β)} {k : α} {h'}
    (h : l'.containsKey k = false) : (l ++ l').getValue k h' = l.getValue k ((containsKey_append_of_not_contains_right h).symm.trans h') := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, ← getValue?_eq_some_getValue, getValue?_append_of_containsKey_eq_false h]

theorem getValueCast?_append_of_containsKey_eq_false [BEq α] [LawfulBEq α] {l l' : List (Σ a, β a)} {k : α}
    (hl' : l'.containsKey k = false) : (l ++ l').getValueCast? k = l.getValueCast? k := by
  rw [getValueCast?_eq_getEntry?, getValueCast?_eq_getEntry?, Option.dmap_congr getEntry?_append,
    Option.dmap_congr (by rw [getEntry?_eq_none.2 hl']), Option.dmap_congr (by rw [Option.or_none])]

theorem getValueCast_append_of_containsKey_eq_false [BEq α] [LawfulBEq α] {l l' : List (Σ a, β a)} {k : α} {h}
    (hl' : l'.containsKey k = false) :
    (l ++ l').getValueCast k h = l.getValueCast k ((containsKey_append_of_not_contains_right hl').symm.trans h) := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, ← getValueCast?_eq_some_getValueCast,
    getValueCast?_append_of_containsKey_eq_false hl']

@[simp]
theorem getKey?_append [BEq α] {l l' : List (Σ a, β a)} {k : α} :
    (l ++ l').getKey? k = (l.getKey? k).or (l'.getKey? k) := by
  simp [getKey?_eq_getEntry?, Option.map_or]

theorem getKey?_append_of_containsKey_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').getKey? k = l.getKey? k := by
  rw [getKey?_append, getKey?_eq_none.2 h, Option.or_none]

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

theorem removeKey_append_of_containsKey_right_eq_false [BEq α] {l l' : List (Σ a, β a)} {k : α}
    (h : l'.containsKey k = false) : (l ++ l').removeKey k = l.removeKey k ++ l' := by
  induction l using assoc_induction
  · simp [removeKey_of_containsKey_eq_false h]
  · next k' v' t ih =>
    rw [cons_append, removeKey_cons, removeKey_cons]
    cases k' == k
    · rw [cond_false, cond_false, ih, cons_append]
    · rw [cond_true, cond_true]

-- TODO: results about combining modification operations

end List
