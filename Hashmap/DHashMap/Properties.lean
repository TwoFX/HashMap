/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Lemmas

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace MyLean.DHashMap

namespace Raw₀

def hasValue [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (b : β) : Prop :=
  ∃ a, m.findConst? a = some b

theorem hasValue_iff_exists [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)} {b : β} :
    m.hasValue b ↔ ∃ a, m.findConst? a = some b := Iff.rfl

@[simp]
theorem hasValue_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} {c} :
    ¬(empty c : Raw₀ α (fun _ => β)).hasValue b := by
  simp [hasValue]

theorem hasValue_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (h : m.1.WF) {a : α} {b b' : β} :
    (m.insert a b).1.hasValue b' ↔ b = b' ∨ ∃ a', (a == a') = false ∧ m.findConst? a' = some b' := by
  simp only [hasValue, findConst?_insert _ h, cond_eq_if]
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

end Raw₀

namespace Raw

def hasValue [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (b : β) : Prop :=
  ∃ a, m.findConst? a = some b

theorem hasValue_iff_exists [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {b : β} :
    m.hasValue b ↔ ∃ a, m.findConst? a = some b := Iff.rfl

theorem hasValue_iff [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {b : β} (h : m.WF) :
    m.hasValue b ↔ Raw₀.hasValue ⟨m, h.size_buckets_pos⟩ b := by
  simp only [hasValue, findConst?_eq h, Raw₀.hasValue]

@[simp]
theorem hasValue_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} {c} :
    ¬(empty c : Raw α (fun _ => β)).hasValue b := by
  simp [hasValue]

@[simp]
theorem hasValue_emptyc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} :
    ¬(∅ : Raw α (fun _ => β)).hasValue b :=
  hasValue_empty

theorem hasValue_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {b b' : β} :
    (m.insert a b).hasValue b' ↔ b = b' ∨ ∃ a', (a == a') = false ∧ m.findConst? a' = some b' := by
  rw [insert_eq h, hasValue_iff, Raw₀.hasValue_insert]
  · simp only [findConst?_eq h]
  · exact h
  · exact h.insert₀

end Raw

def hasValue [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (b : β) : Prop :=
  ∃ a, m.findConst? a = some b

theorem hasValue_iff_exists [BEq α] [Hashable α] {m : DHashMap α (fun _ => β)} {b : β} :
    m.hasValue b ↔ ∃ a, m.findConst? a = some b := Iff.rfl

@[simp]
theorem hasValue_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} {c} :
    ¬(empty c : DHashMap α (fun _ => β)).hasValue b := by
  simp [hasValue]

@[simp]
theorem hasValue_emptyc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {b : β} :
    ¬(∅ : DHashMap α (fun _ => β)).hasValue b :=
  hasValue_empty

theorem hasValue_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : DHashMap α (fun _ => β)} {a : α} {b b' : β} :
    (m.insert a b).hasValue b' ↔ b = b' ∨ ∃ a', (a == a') = false ∧ m.findConst? a' = some b' :=
  Raw₀.hasValue_insert m.2

end MyLean.DHashMap
