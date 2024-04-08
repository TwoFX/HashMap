/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.AssocList.Basic

namespace Lean

def AssocListMap (α : Type u) [BEq α] (β : α → Type v) :=
  { l : AssocList α β // l.WF }

abbrev AssocListMap' (α : Type u) [BEq α] (β : Type v) :=
  AssocListMap α (fun _ => β)

theorem AssocListMap.ext [BEq α] {l l' : AssocListMap α β} : l.1 = l'.1 → l = l' := by
  cases l; cases l'; rintro rfl; rfl

namespace AssocListMap

def nil [BEq α] : AssocListMap α β :=
  ⟨AssocList.nil, AssocList.WF_nil⟩

def findEntry? [BEq α] (a : α) : AssocListMap α β → Option (Σ a, β a) :=
  fun l => l.1.findEntry? a

@[simp]
theorem findEntry?_nil [BEq α] {a : α} : (nil : AssocListMap α β).findEntry? a = none :=
  AssocList.findEntry?_nil

theorem findEntry?_eq_of_beq [BEq α] [EquivBEq α] {l : AssocListMap α β} {a a' : α} (h : a == a') :
    l.findEntry? a = l.findEntry? a' :=
  AssocList.findEntry?_eq_of_beq h

def find? [BEq α] (a : α) : AssocListMap' α β → Option β :=
  fun l => l.1.find? a

@[simp]
theorem find?_nil [BEq α] {a : α} : (nil : AssocListMap' α β).find? a = none :=
  AssocList.find?_nil

theorem find?_eq_findEntry? [BEq α] {l : AssocListMap' α β} {a : α} :
    l.find? a = (l.findEntry? a).map (·.2) :=
  AssocList.find?_eq_findEntry?

theorem find?_eq_of_beq [BEq α] [EquivBEq α] {l : AssocListMap' α β} {a a' : α} (h : a == a') :
    l.find? a = l.find? a' :=
  AssocList.find?_eq_of_beq h

def findKey? [BEq α] (a : α) : AssocListMap α β → Option α :=
  fun l => l.1.findKey? a

@[simp]
theorem findKey?_nil [BEq α] {a : α} : (nil : AssocListMap α β).findKey? a = none :=
  AssocList.findKey?_nil

theorem findKey?_eq_findEntry? [BEq α] {l : AssocListMap α β} {a : α} :
    l.findKey? a = (l.findEntry? a).map (·.1) :=
  AssocList.findKey?_eq_findEntry?

theorem findKey?_eq_of_beq [BEq α] [EquivBEq α] {l : AssocListMap α β} {a a' : α} (h : a == a') :
    l.findKey? a = l.findKey? a' :=
  AssocList.findKey?_eq_of_beq h

def contains [BEq α] (a : α) : AssocListMap α β → Bool :=
  fun l => l.1.contains a

@[simp]
theorem contains_nil [BEq α] {a : α} : (nil : AssocListMap α β).contains a = false :=
  AssocList.contains_nil

theorem contains_eq_isSome_findEntry? [BEq α] {l : AssocListMap α β} :
    l.contains a = (l.findEntry? a).isSome :=
  AssocList.contains_eq_isSome_findEntry?

theorem contains_eq_isSome_find? [BEq α] {l : AssocListMap' α β} :
    l.contains a = (l.find? a).isSome :=
  AssocList.contains_eq_isSome_find?

theorem contains_eq_isSome_findKey? [BEq α] {l : AssocListMap α β} :
    l.contains a = (l.findKey? a).isSome :=
  AssocList.contains_eq_isSome_findKey?

theorem contains_eq_of_beq [BEq α] [EquivBEq α] {l : AssocListMap α β} {a b : α} (h : a == b) :
    l.contains a = l.contains b :=
  AssocList.contains_eq_of_beq h

theorem contains_of_beq [BEq α] [EquivBEq α] {l : AssocListMap α β} {a b : α} (hla : l.contains a)
    (hab : a == b) : l.contains b :=
  AssocList.contains_of_beq hla hab

/- Skipping findEntry, findKey, find for now. -/

/- Skipping replace and cons (with proof arguments) for now. -/

def erase [BEq α] [EquivBEq α] (a : α) : AssocListMap α β → AssocListMap α β :=
  fun l => ⟨l.1.erase a, AssocList.WF_erase l.2⟩

@[simp]
theorem erase_nil [BEq α] [EquivBEq α] {a : α} : (nil : AssocListMap α β).erase a = nil :=
  AssocListMap.ext <| AssocList.erase_nil (a := a)

@[simp]
theorem findEntry?_erase_self [BEq α] [EquivBEq α] {l : AssocListMap α β} {k : α} :
    (l.erase k).findEntry? k = none :=
  AssocList.findEntry?_erase_self l.2

theorem findEntry?_erase_of_beq [BEq α] [EquivBEq α] {l : AssocListMap α β} {k a : α} (h : k == a) :
    (l.erase k).findEntry? a = none :=
  AssocList.findEntry?_erase_of_beq l.2 h

theorem findEntry?_erase_of_false [BEq α] [EquivBEq α] {l : AssocListMap α β} {k a : α}
    (h : (k == a) = false) : (l.erase k).findEntry? a = l.findEntry? a :=
  AssocList.findEntry?_erase_of_false h

theorem findEntry?_erase [BEq α] [EquivBEq α] {l : AssocListMap α β} {k a : α} :
    (l.erase k).findEntry? a = bif k == a then none else l.findEntry? a :=
  AssocList.findEntry?_erase l.2

/- Skipping findKey?_erase, find?_erase and contains_erase for now. -/

def insert [BEq α] [EquivBEq α] (k : α) (v : β k) : AssocListMap α β → AssocListMap α β :=
  fun l => ⟨l.1.insert k v, AssocList.WF_insert l.2⟩

/- Skipping findEntry?_insert, findKey?_insert, find?_insert and contains_insert for now. -/

end AssocListMap

end Lean
