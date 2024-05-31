/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Properties
import Hashmap.HashMap.Lemmas

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace MyLean.HashMap

namespace Raw

def hasValue [BEq α] [Hashable α] (m : Raw α β) (b : β) : Prop :=
  ∃ a, m.find? a = some b

theorem hasValue_iff_exists [BEq α] [Hashable α] {m : Raw α β} {b : β} :
    m.hasValue b ↔ ∃ a, m.find? a = some b := Iff.rfl

theorem hasValue_iff [BEq α] [Hashable α] {m : Raw α β} {b : β} :
    m.hasValue b ↔ m.1.hasValue b := Iff.rfl

@[simp]
theorem hasValue_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} {c} :
    ¬(empty c : Raw α β).hasValue b :=
  DHashMap.Raw.hasValue_empty

@[simp]
theorem hasValue_emptyc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} :
    ¬(∅ : Raw α β).hasValue b :=
  DHashMap.Raw.hasValue_emptyc

theorem hasValue_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw α β} (h : m.WF) {a : α} {b b' : β} :
    (m.insert a b).hasValue b' ↔ b = b' ∨ ∃ a', (a == a') = false ∧ m.find? a' = some b' :=
  DHashMap.Raw.hasValue_insert h

end Raw

def hasValue [BEq α] [Hashable α] (m : HashMap α β) (b : β) : Prop :=
  ∃ a, m.find? a = some b

theorem hasValue_iff_exists [BEq α] [Hashable α] {m : HashMap α β} {b : β} :
    m.hasValue b ↔ ∃ a, m.find? a = some b := Iff.rfl

theorem hasValue_iff [BEq α] [Hashable α] {m : HashMap α β} {b : β} :
    m.hasValue b ↔ m.1.hasValue b := Iff.rfl

@[simp]
theorem hasValue_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} {c} :
    ¬(empty c : HashMap α β).hasValue b :=
  DHashMap.hasValue_empty

@[simp]
theorem hasValue_emptyc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} :
    ¬(∅ : HashMap α β).hasValue b :=
  DHashMap.Raw.hasValue_emptyc

theorem hasValue_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : HashMap α β} {a : α} {b b' : β} :
    (m.insert a b).hasValue b' ↔ b = b' ∨ ∃ a', (a == a') = false ∧ m.find? a' = some b' :=
  DHashMap.hasValue_insert

end MyLean.HashMap
