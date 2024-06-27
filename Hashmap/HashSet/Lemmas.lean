/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.HashMap.Lemmas
import Hashmap.HashSet.Basic

set_option autoImplicit false

universe u v

variable {α : Type u} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace Std.HashSet

namespace Raw

variable {m : Raw α} (h : m.WF)

private theorem ext {m m' : Raw α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} : (m.insert a).isEmpty = false :=
  HashMap.Raw.isEmpty_insert h.out

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m.contains a = m.contains b :=
  HashMap.Raw.contains_congr h.out hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  HashMap.Raw.mem_congr h.out hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α).contains a = false :=
  HashMap.Raw.contains_empty

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  HashMap.Raw.mem_iff_contains

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α) :=
  HashMap.Raw.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α).contains a = false :=
  HashMap.Raw.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α) :=
  HashMap.Raw.not_mem_emptyc

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} : (m.insert k).contains a = (a == k || m.contains a) :=
  HashMap.Raw.contains_insert h.out

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k ↔ a == k ∨ a ∈ m :=
  HashMap.Raw.mem_insert h.out

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → (a == k) = false → m.contains a :=
  HashMap.Raw.contains_of_contains_insert h.out

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → (a == k) = false → a ∈ m :=
  HashMap.Raw.mem_of_mem_insert h.out

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α}  : (m.insert k).contains k :=
  HashMap.Raw.contains_insert_self h.out

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.insert k :=
  HashMap.Raw.mem_insert_self h.out

@[simp]
theorem size_empty {c} : (empty c : Raw α).size = 0 :=
  HashMap.Raw.size_empty

@[simp]
theorem size_emptyc : (∅ : Raw α).size = 0 :=
  HashMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  HashMap.Raw.isEmpty_eq_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).size = bif m.contains k then m.size else m.size + 1 :=
  HashMap.Raw.size_insert h.out

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size :=
  HashMap.Raw.size_le_size_insert h.out

@[simp]
theorem remove_empty {k : α} {c : Nat} : (empty c : Raw α).remove k = empty c :=
  ext HashMap.Raw.remove_empty

@[simp]
theorem remove_emptyc {k : α} : (∅ : Raw α).remove k = ∅ :=
  ext HashMap.Raw.remove_emptyc

@[simp]
theorem isEmpty_remove [EquivBEq α] [LawfulHashable α] {k : α} : (m.remove k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  HashMap.Raw.isEmpty_remove h.out

@[simp]
theorem contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a = (!(a == k) && m.contains a) :=
  HashMap.Raw.contains_remove h.out

@[simp]
theorem mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k ↔ (a == k) = false ∧ a ∈ m :=
  HashMap.Raw.mem_remove h.out

theorem contains_of_contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a → m.contains a :=
  HashMap.Raw.contains_of_contains_remove h.out

theorem mem_of_mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k → a ∈ m :=
  HashMap.Raw.mem_of_mem_remove h.out

theorem size_remove [EquivBEq α] [LawfulHashable α] {k : α} : (m.remove k).size = bif m.contains k then m.size - 1 else m.size :=
  HashMap.Raw.size_remove h.out

theorem size_remove_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.remove k).size ≤ m.size :=
  HashMap.Raw.size_remove_le h.out

@[simp]
theorem fst_containsThenInsert {k : α} : (m.containsThenInsert k).1 = m.insert k :=
  ext (HashMap.Raw.fst_containsThenInsert h.out)

@[simp]
theorem snd_containsThenInsert {k : α} : (m.containsThenInsert k).2 = m.contains k :=
  HashMap.Raw.snd_containsThenInsert h.out

end Raw

section

variable {m : HashSet α}

private theorem ext {m m' : HashSet α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem isEmpty_empty {c} : (empty c : HashSet α).isEmpty :=
  HashMap.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : HashSet α).isEmpty :=
  HashMap.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} : (m.insert a).isEmpty = false :=
  HashMap.isEmpty_insert

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m.contains a = m.contains b :=
  HashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  HashMap.mem_congr hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : HashSet α).contains a = false :=
  HashMap.contains_empty

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  HashMap.mem_iff_contains

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : HashSet α) :=
  HashMap.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : HashSet α).contains a = false :=
  HashMap.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : HashSet α) :=
  HashMap.not_mem_emptyc

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} : (m.insert k).contains a = (a == k || m.contains a) :=
  HashMap.contains_insert

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k ↔ a == k ∨ a ∈ m :=
  HashMap.mem_insert

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → (a == k) = false → m.contains a :=
  HashMap.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → (a == k) = false → a ∈ m :=
  HashMap.mem_of_mem_insert

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α}  : (m.insert k).contains k :=
  HashMap.contains_insert_self

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.insert k :=
  HashMap.mem_insert_self

@[simp]
theorem size_empty {c} : (empty c : HashSet α).size = 0 :=
  HashMap.size_empty

@[simp]
theorem size_emptyc : (∅ : HashSet α).size = 0 :=
  HashMap.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  HashMap.isEmpty_eq_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).size = bif m.contains k then m.size else m.size + 1 :=
  HashMap.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size :=
  HashMap.size_le_size_insert

@[simp]
theorem remove_empty {a : α} {c : Nat} : (empty c : HashSet α).remove a = empty c :=
  ext HashMap.remove_empty

@[simp]
theorem remove_emptyc {a : α} : (∅ : HashSet α).remove a = ∅ :=
  ext HashMap.remove_emptyc

@[simp]
theorem isEmpty_remove [EquivBEq α] [LawfulHashable α] {k : α} : (m.remove k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  HashMap.isEmpty_remove

@[simp]
theorem contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a = (!(a == k) && m.contains a) :=
  HashMap.contains_remove

@[simp]
theorem mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k ↔ (a == k) = false ∧ a ∈ m :=
  HashMap.mem_remove

theorem contains_of_contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a → m.contains a :=
  HashMap.contains_of_contains_remove

theorem mem_of_mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k → a ∈ m :=
  HashMap.mem_of_mem_remove

theorem size_remove [EquivBEq α] [LawfulHashable α] {k : α} : (m.remove k).size = bif m.contains k then m.size - 1 else m.size :=
  HashMap.size_remove

theorem size_remove_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.remove k).size ≤ m.size :=
  HashMap.size_remove_le

@[simp]
theorem fst_containsThenInsert {k : α} : (m.containsThenInsert k).1 = m.insert k :=
  ext HashMap.fst_containsThenInsert

@[simp]
theorem snd_containsThenInsert {k : α} : (m.containsThenInsert k).2 = m.contains k :=
  HashMap.snd_containsThenInsert

end

end Std.HashSet
