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
theorem findEntry?_eq [BEq α] {l : AssocList α β} {a : α} : l.findEntry? a = l.toList.findEntry? a := by
  induction l <;> simp_all [findEntry?, List.findEntry?]

@[simp]
theorem find?_eq {β : Type v} [BEq α] {l : AssocList α (fun _ => β)} {a : α} : l.find? a = l.toList.findValue? a := by
  induction l <;> simp_all [find?, List.findValue?]

@[simp]
theorem findCast?_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} : l.findCast? a = l.toList.findValueCast? a := by
  induction l <;> simp_all [findCast?, List.findValueCast?]

@[simp]
theorem findKey?_eq [BEq α] {l : AssocList α β} {a : α} : l.findKey? a = l.toList.findKey? a := by
  induction l <;> simp_all [findKey?, List.findKey?]

@[simp]
theorem contains_eq [BEq α] {l : AssocList α β} {a : α} : l.contains a = l.toList.containsKey a := by
  induction l <;> simp_all [contains, List.containsKey]

@[simp]
theorem toList_replace [BEq α] {l : AssocList α β} {a : α} {b : β a} :
    (l.replace a b).toList = l.toList.replaceEntry a b := by
  induction l
  · simp [replace]
  · next k v t ih => cases h : k == a <;> simp_all [replace, List.replaceEntry_cons]

@[simp]
theorem toList_erase [BEq α] {l : AssocList α β} {a : α} : (l.erase a).toList = l.toList.eraseKey a := by
  induction l
  · simp [erase]
  · next k v t ih => cases h : k == a <;> simp_all [erase, List.eraseKey_cons]

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

theorem findEntry?_eq_some [BEq α] {l : AssocList α β} {a : α} {p : Σ a, β a}
    (h : l.findEntry? a = some p) : p.1 == a :=
  List.findEntry?_eq_some (findEntry?_eq (l := l) ▸ h)

end MyLean.AssocList
