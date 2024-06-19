/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.AssocList.Basic
import Hashmap.List.Associative

set_option autoImplicit false

universe w v u

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace MyLean.AssocList

@[simp] theorem toList_nil : (nil : AssocList α β).toList = [] := rfl
@[simp] theorem toList_cons {l : AssocList α β} {a : α} {b : β a} : (l.cons a b).toList = ⟨a, b⟩ :: l.toList := rfl

@[simp]
theorem foldl_eq {f : δ → (a : α) → β a → δ} {init : δ} {l : AssocList α β} :
    l.foldl f init = l.toList.foldl (fun d p => f d p.1 p.2) init := by
  induction l generalizing init <;> simp_all [foldl, Id.run, foldlM]


@[simp]
theorem length_eq {l : AssocList α β} : l.length = l.toList.length := by
  rw [length, foldl_eq]
  suffices ∀ n, l.toList.foldl (fun d _ => d + 1) n = l.toList.length + n by simpa using this 0
  induction l
  · simp
  · next _ _ t ih =>
    intro n
    simp [ih, Nat.add_assoc, Nat.add_comm n 1]

@[simp]
theorem getEntry?_eq [BEq α] {l : AssocList α β} {a : α} : l.getEntry? a = l.toList.getEntry? a := by
  induction l <;> simp_all [getEntry?, List.getEntry?]

@[simp]
theorem get?_eq {β : Type v} [BEq α] {l : AssocList α (fun _ => β)} {a : α} : l.get? a = l.toList.getValue? a := by
  induction l <;> simp_all [get?, List.getValue?]

@[simp]
theorem getCast?_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} : l.getCast? a = l.toList.getValueCast? a := by
  induction l <;> simp_all [getCast?, List.getValueCast?]

@[simp]
theorem getWithCast?_eq [BEq α] {l : AssocList α β} {a : α} {cast : ∀ {b}, b == a → β b → β a} :
    l.getWithCast? a cast = l.toList.getValueWithCast? a cast := by
  induction l <;> simp_all [getWithCast?, List.getValueWithCast?]

@[simp]
theorem getKey?_eq [BEq α] {l : AssocList α β} {a : α} : l.getKey? a = l.toList.getKey? a := by
  induction l <;> simp_all [getKey?, List.getKey?]

@[simp]
theorem contains_eq [BEq α] {l : AssocList α β} {a : α} : l.contains a = l.toList.containsKey a := by
  induction l <;> simp_all [contains, List.containsKey]

@[simp]
theorem getCast_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} {h} :
    l.getCast a h = l.toList.getValueCast a (contains_eq.symm.trans h) := by
  induction l
  · simp [contains] at h
  · next k v t ih => simp only [getCast, toList_cons, List.getValueCast_cons, ih]

@[simp]
theorem get_eq {β : Type v} [BEq α] {l : AssocList α (fun _ => β)} {a : α} {h} :
    l.get a h = l.toList.getValue a (contains_eq.symm.trans h) := by
  induction l
  · simp [contains] at h
  · next k v t ih => simp only [get, toList_cons, List.getValue_cons, ih]

@[simp]
theorem getCastD_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} {fallback : β a} :
    l.getCastD a fallback = l.toList.getValueCastD a fallback := by
  induction l
  · simp [getCastD, List.getValueCastD]
  · simp_all [getCastD, List.getValueCastD, List.getValueCastD, List.getValueCast?_cons,
      apply_dite (fun x => Option.getD x fallback)]

@[simp]
theorem getD_eq {β : Type v} [BEq α] {l : AssocList α (fun _ => β)} {a : α} {fallback : β} :
    l.getD a fallback = l.toList.getValueD a fallback := by
  induction l
  · simp [getD, List.getValueD]
  · simp_all [getD, List.getValueD, List.getValueD, List.getValue?_cons, apply_bif (fun x => Option.getD x fallback)]

@[simp]
theorem panicWithPosWithDecl_eq [Inhabited α] {modName declName line col msg} :
  panicWithPosWithDecl modName declName line col msg = (default : α) := rfl

@[simp] theorem Option.get!_none [Inhabited α] : (none : Option α).get! = default := rfl
@[simp] theorem Option.get!_some [Inhabited α] {a : α} : (some a).get! = a := rfl

@[simp]
theorem getCast!_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} [Inhabited (β a)] :
    l.getCast! a = l.toList.getValueCast! a := by
  induction l
  · simp [getCast!, List.getValueCast!]
  · simp_all [getCast!, List.getValueCast!, List.getValueCast!, List.getValueCast?_cons,
      apply_dite Option.get!]

@[simp]
theorem get!_eq {β : Type v} [BEq α] [Inhabited β] {l : AssocList α (fun _ => β)} {a : α} :
    l.get! a = l.toList.getValue! a := by
  induction l
  · simp [get!, List.getValue!]
  · simp_all [get!, List.getValue!, List.getValue!, List.getValue?_cons, apply_bif Option.get!]

@[simp]
theorem toList_replace [BEq α] {l : AssocList α β} {a : α} {b : β a} :
    (l.replace a b).toList = l.toList.replaceEntry a b := by
  induction l
  · simp [replace]
  · next k v t ih => cases h : k == a <;> simp_all [replace, List.replaceEntry_cons]

@[simp]
theorem toList_remove [BEq α] {l : AssocList α β} {a : α} : (l.remove a).toList = l.toList.removeKey a := by
  induction l
  · simp [remove]
  · next k v t ih => cases h : k == a <;> simp_all [remove, List.removeKey_cons]

@[simp]
theorem toList_insert [BEq α] {l : AssocList α β} {k : α} {v : β k} :
    (l.insert k v).toList = l.toList.insertEntry k v := by
  simp [insert, List.insertEntry, apply_bif toList]

open List

theorem toList_filterMap {f : (a : α) → β a → Option (γ a)} {l : AssocList α β} :
    (l.filterMap f).toList ~ l.toList.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩) := by
  rw [filterMap]
  suffices ∀ l l', (filterMap.go f l l').toList ~ l.toList ++ l'.toList.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩) by
    simpa using this .nil l
  intros l l'
  induction l' generalizing l
  · simp [filterMap.go]
  · next k v t ih =>
    simp only [filterMap.go, toList_cons, filterMap_cons]
    split
    · next h => exact (ih _).trans (by simp [h])
    · next h =>
      refine (ih _).trans ?_
      simp only [toList_cons, cons_append]
      exact perm_middle.symm.trans (by simp [h])

theorem toList_map {f : (a : α) → β a → γ a} {l : AssocList α β} :
    (l.map f).toList ~ l.toList.map fun p => ⟨p.1, f p.1 p.2⟩ := by
  rw [map]
  suffices ∀ l l', (map.go f l l').toList ~ l.toList ++ l'.toList.map fun p => ⟨p.1, f p.1 p.2⟩ by
    simpa using this .nil l
  intros l l'
  induction l' generalizing l
  · simp [map.go]
  · next k v t ih =>
    simp only [map.go, toList_cons, map_cons]
    refine (ih _).trans ?_
    simpa using perm_middle.symm

theorem getEntry?_eq_some [BEq α] {l : AssocList α β} {a : α} {p : Σ a, β a}
    (h : l.getEntry? a = some p) : p.1 == a :=
  List.getEntry?_eq_some (getEntry?_eq (l := l) ▸ h)

end MyLean.AssocList
