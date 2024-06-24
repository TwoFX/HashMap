/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Lemmas
import Hashmap.HashMap.Basic

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

namespace MyLean.HashMap

namespace Raw

variable {m : Raw α β} (h : m.WF)

private theorem ext {m m' : Raw α β} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α β).isEmpty :=
  DHashMap.Raw.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α β).isEmpty :=
  DHashMap.Raw.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : (m.insert a b).isEmpty = false :=
  DHashMap.Raw.isEmpty_insert h.out

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m.contains a = m.contains b :=
  DHashMap.Raw.contains_congr h.out hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  DHashMap.Raw.mem_congr h.out hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α β).contains a = false :=
  DHashMap.Raw.contains_empty

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  DHashMap.Raw.mem_iff_contains

@[simp] theorem get_eq_getElem {a : α} {h} : get m a h = m[a]'h := rfl
@[simp] theorem get?_eq_getElem? {a : α} : get? m a = m[a]? := rfl
@[simp] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! m a = m[a]! := rfl

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α β) :=
  DHashMap.Raw.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false :=
  DHashMap.Raw.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α β) :=
  DHashMap.Raw.not_mem_emptyc

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} : (m.insert a b).contains k = (a == k || m.contains k) :=
  DHashMap.Raw.contains_insert h.out

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} : k ∈ m.insert a b ↔ a == k ∨ k ∈ m :=
  DHashMap.Raw.mem_insert h.out

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insert a b).contains k → (a == k) = false → m.contains k :=
  DHashMap.Raw.contains_of_contains_insert h.out

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    k ∈ m.insert a b → (a == k) = false → k ∈ m :=
  DHashMap.Raw.mem_of_mem_insert h.out

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : (m.insert a b).contains a :=
  DHashMap.Raw.contains_insert_self h.out

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : a ∈ m.insert a b :=
  DHashMap.Raw.mem_insert_self h.out

@[simp]
theorem size_empty {c} : (empty c : Raw α β).size = 0 :=
  DHashMap.Raw.size_empty

@[simp]
theorem size_emptyc : (∅ : Raw α β).size = 0 :=
  DHashMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  DHashMap.Raw.isEmpty_eq_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : (m.insert a b).size = bif m.contains a then m.size else m.size + 1 :=
  DHashMap.Raw.size_insert h.out

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : m.size ≤ (m.insert a b).size :=
  DHashMap.Raw.size_le_size_insert h.out

@[simp]
theorem remove_empty {a : α} {c : Nat} : (empty c : Raw α β).remove a = empty c :=
  ext DHashMap.Raw.remove_empty

@[simp]
theorem remove_emptyc {a : α} : (∅ : Raw α β).remove a = ∅ :=
  ext DHashMap.Raw.remove_emptyc

@[simp]
theorem isEmpty_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).isEmpty = (m.isEmpty || (m.size == 1 && m.contains a)) :=
  DHashMap.Raw.isEmpty_remove h.out

@[simp]
theorem contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a = (!(k == a) && m.contains a) :=
  DHashMap.Raw.contains_remove h.out

@[simp]
theorem mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k ↔ (k == a) = false ∧ a ∈ m :=
  DHashMap.Raw.mem_remove h.out

theorem contains_of_contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a → m.contains a :=
  DHashMap.Raw.contains_of_contains_remove h.out

theorem mem_of_mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k → a ∈ m :=
  DHashMap.Raw.mem_of_mem_remove h.out

theorem size_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).size = bif m.contains a then m.size - 1 else m.size :=
  DHashMap.Raw.size_remove h.out

theorem size_remove_le [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).size ≤ m.size :=
  DHashMap.Raw.size_remove_le h.out

@[simp]
theorem fst_containsThenInsert {a : α} {b : β} : (m.containsThenInsert a b).1 = m.insert a b :=
  ext (DHashMap.Raw.fst_containsThenInsert h.out)

@[simp]
theorem snd_containsThenInsert {a : α} {b : β} : (m.containsThenInsert a b).2 = m.contains a :=
  DHashMap.Raw.snd_containsThenInsert h.out

@[simp]
theorem getElem?_empty {a : α} {c} : (empty c : Raw α β)[a]? = none :=
  DHashMap.Raw.Const.get?_empty

@[simp]
theorem getElem?_emptyc {a : α} : (∅ : Raw α β)[a]? = none :=
  DHashMap.Raw.Const.get?_emptyc

theorem getElem?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m[a]? = none :=
  DHashMap.Raw.Const.get?_of_isEmpty h.out

theorem getElem?_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insert a b)[k]? = bif a == k then some b else m[k]? :=
  DHashMap.Raw.Const.get?_insert h.out

@[simp]
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insert a b)[a]? = some b :=
  DHashMap.Raw.Const.get?_insert_self h.out

theorem contains_eq_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = m[a]?.isSome :=
  DHashMap.Raw.Const.contains_eq_isSome_get? h.out

theorem getElem?_remove [EquivBEq α] [LawfulHashable α] {a k : α} :
    (m.remove a)[k]? = bif a == k then none else m[k]? :=
  DHashMap.Raw.Const.get?_remove h.out

@[simp]
theorem getElem?_remove_self [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a)[a]? = none :=
  DHashMap.Raw.Const.get?_remove_self h.out

theorem getElem?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m[a]? = m[b]? :=
  DHashMap.Raw.Const.get?_congr h.out hab

theorem getElem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    (m.insert a b)[k]'h₁ = if h₂ : a == k then b else m[k]'(mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) :=
  DHashMap.Raw.Const.get_insert (h₁ := h₁) h.out

@[simp]
theorem getElem_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insert a b)[a]'(mem_insert_self h) = b :=
  DHashMap.Raw.Const.get_insert_self h.out

theorem getElem_remove [EquivBEq α] [LawfulHashable α] {a k : α} {h'} :
    (m.remove a)[k]'h' = m[k]'(mem_of_mem_remove h h') :=
  DHashMap.Raw.Const.get_remove (h' := h') h.out

theorem getElem?_eq_some_getElem [EquivBEq α] [LawfulHashable α] {a : α} {h' : a ∈ m} : m[a]? = some (m[a]'h') :=
  @DHashMap.Raw.Const.get?_eq_some_get _ _ _ _ _ h.out _ _ _ h'

theorem getElem_congr [LawfulBEq α] {a b : α} (hab : a == b) {h'} : m[a]'h' = m[b]'((mem_congr h hab).1 h') :=
  DHashMap.Raw.Const.get_congr h.out hab (h' := h')

@[simp]
theorem getElem!_empty [Inhabited β] {a : α} {c} : (empty c : Raw α β)[a]! = default :=
  DHashMap.Raw.Const.get!_empty

@[simp]
theorem getElem!_emptyc [Inhabited β] {a : α} : (∅ : Raw α β)[a]! = default :=
  DHashMap.Raw.Const.get!_emptyc

theorem getElem!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m.isEmpty = true → m[a]! = default :=
  DHashMap.Raw.Const.get!_of_isEmpty h.out

theorem getElem!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    (m.insert a b)[k]! = bif a == k then b else m[k]! :=
  DHashMap.Raw.Const.get!_insert h.out

@[simp]
theorem getElem!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {b : β} :
    (m.insert a b)[a]! = b :=
  DHashMap.Raw.Const.get!_insert_self h.out

theorem getElem!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = false → m[a]! = default :=
  DHashMap.Raw.Const.get!_eq_default_of_contains_eq_false h.out

theorem getElem!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    ¬a ∈ m → m[a]! = default :=
  DHashMap.Raw.Const.get!_eq_default h.out

theorem getElem!_remove [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} :
    (m.remove a)[k]! = bif a == k then default else m[k]! :=
  DHashMap.Raw.Const.get!_remove h.out

@[simp]
theorem getElem!_remove_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    (m.remove k)[k]! = default :=
  DHashMap.Raw.Const.get!_remove_self h.out

theorem getElem?_eq_some_getElem!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = true → m[a]? = some m[a]! :=
  DHashMap.Raw.Const.get?_eq_some_get!_of_contains h.out

theorem getElem?_eq_some_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    a ∈ m → m[a]? = some m[a]! :=
  DHashMap.Raw.Const.get?_eq_some_get! h.out

theorem getElem!_eq_get!_getElem? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m[a]?.get! :=
  DHashMap.Raw.Const.get!_eq_get!_get? h.out

theorem getElem_eq_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h'} :
    m[a]'h' = m[a]! :=
  @DHashMap.Raw.Const.get_eq_get! _ _ _ _ _ h.out _ _ _ _ h'

theorem getElem!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    m[a]! = m[b]! :=
  DHashMap.Raw.Const.get!_congr h.out hab

@[simp]
theorem getD_empty {a : α} {fallback : β} {c} : (empty c : Raw α β).getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_empty

@[simp]
theorem getD_emptyc {a : α} {fallback : β} : (∅ : Raw α β).getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.isEmpty = true → m.getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_of_isEmpty h.out

theorem getD_insert [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    (m.insert a b).getD k fallback = bif a == k then b else m.getD k fallback :=
  DHashMap.Raw.Const.getD_insert h.out

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {fallback b : β} :
   (m.insert a b).getD a fallback = b :=
  DHashMap.Raw.Const.getD_insert_self h.out

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = false → m.getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_eq_fallback_of_contains_eq_false h.out

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_eq_fallback h.out

theorem getD_remove [EquivBEq α] [LawfulHashable α] {a k : α} {fallback : β} :
    (m.remove a).getD k fallback = bif a == k then fallback else m.getD k fallback :=
  DHashMap.Raw.Const.getD_remove h.out

@[simp]
theorem getD_remove_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    (m.remove k).getD k fallback = fallback :=
  DHashMap.Raw.Const.getD_remove_self h.out

theorem getElem?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → m[a]? = some (m.getD a fallback) :=
  DHashMap.Raw.Const.get?_eq_some_getD_of_contains h.out

theorem getElem?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    a ∈ m → m[a]? = some (m.getD a fallback) :=
  DHashMap.Raw.Const.get?_eq_some_getD h.out

theorem getD_eq_getD_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.getD a fallback = m[a]?.getD fallback :=
  DHashMap.Raw.Const.getD_eq_getD_get? h.out

theorem getElem_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h'} :
    m[a]'h' = m.getD a fallback :=
  @DHashMap.Raw.Const.get_eq_getD _ _ _ _ _ h.out _ _ _ _ h'

theorem getElem!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m.getD a default :=
  DHashMap.Raw.Const.get!_eq_getD_default h.out

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    m.getD a fallback = m.getD b fallback :=
  DHashMap.Raw.Const.getD_congr h.out hab

@[simp]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insertIfNew a b).isEmpty = false :=
  DHashMap.Raw.isEmpty_insertIfNew h.out

@[simp]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insertIfNew a b).contains k = (a == k || m.contains k) :=
  DHashMap.Raw.contains_insertIfNew h.out

@[simp]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    k ∈ m.insertIfNew a b ↔ a == k ∨ k ∈ m :=
  DHashMap.Raw.mem_insertIfNew h.out

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof obligation in the statement of
    `getElem_insertIfNew`. -/
theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insertIfNew a b).contains k → ¬((a == k) ∧ m.contains a = false) → m.contains k :=
  DHashMap.Raw.contains_of_contains_insertIfNew h.out

/-- This is a restatement of `mem_insertIfNew` that is written to exactly match the proof obligation in the statement of
    `getElem_insertIfNew`. -/
theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    k ∈ m.insertIfNew a b → ¬((a == k) ∧ ¬a ∈ m) → k ∈ m :=
  DHashMap.Raw.mem_of_mem_insertIfNew h.out

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insertIfNew a b).size = bif m.contains a then m.size else m.size + 1 :=
  DHashMap.Raw.size_insertIfNew h.out

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    m.size ≤ (m.insertIfNew a b).size :=
  DHashMap.Raw.size_le_size_insertIfNew h.out

theorem getElem?_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insertIfNew a b)[k]? = bif a == k && !m.contains a then some b else m[k]? :=
  DHashMap.Raw.Const.get?_insertIfNew h.out

theorem getElem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    (m.insertIfNew a b)[k]'h₁ = if h₂ : a == k ∧ ¬a ∈ m then b else m[k]'(mem_of_mem_insertIfNew h h₁ h₂) :=
  DHashMap.Raw.Const.get_insertIfNew h.out (h₁ := h₁)

theorem getElem!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    (m.insertIfNew a b)[k]! = bif a == k && !m.contains a then b else m[k]! :=
  DHashMap.Raw.Const.get!_insertIfNew h.out

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    (m.insertIfNew a b).getD k fallback = bif a == k && !m.contains a then b else m.getD k fallback :=
  DHashMap.Raw.Const.getD_insertIfNew h.out

@[simp]
theorem fst_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).1 = m.insertIfNew a b :=
  ext (DHashMap.Raw.Const.fst_getThenInsertIfNew? h.out)

@[simp]
theorem snd_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).2 = get? m a :=
  DHashMap.Raw.Const.snd_getThenInsertIfNew? h.out

end Raw

section

variable {m : HashMap α β}

private theorem ext {m m' : HashMap α β} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem isEmpty_empty {c} : (empty c : HashMap α β).isEmpty :=
  DHashMap.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : HashMap α β).isEmpty :=
  DHashMap.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : (m.insert a b).isEmpty = false :=
  DHashMap.isEmpty_insert

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m.contains a = m.contains b :=
  DHashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  DHashMap.mem_congr hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : HashMap α β).contains a = false :=
  DHashMap.contains_empty

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  DHashMap.mem_iff_contains

@[simp] theorem get_eq_getElem {a : α} {h} : get m a h = m[a]'h := rfl
@[simp] theorem get?_eq_getElem? {a : α} : get? m a = m[a]? := rfl
@[simp] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! m a = m[a]! := rfl

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : HashMap α β) :=
  DHashMap.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : HashMap α β).contains a = false :=
  DHashMap.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : HashMap α β) :=
  DHashMap.not_mem_emptyc

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} : (m.insert a b).contains k = (a == k || m.contains k) :=
  DHashMap.contains_insert

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} : k ∈ m.insert a b ↔ a == k ∨ k ∈ m :=
  DHashMap.mem_insert

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insert a b).contains k → (a == k) = false → m.contains k :=
  DHashMap.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    k ∈ m.insert a b → (a == k) = false → k ∈ m :=
  DHashMap.mem_of_mem_insert

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : (m.insert a b).contains a :=
  DHashMap.contains_insert_self

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : a ∈ m.insert a b :=
  DHashMap.mem_insert_self

@[simp]
theorem size_empty {c} : (empty c : HashMap α β).size = 0 :=
  DHashMap.size_empty

@[simp]
theorem size_emptyc : (∅ : HashMap α β).size = 0 :=
  DHashMap.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  DHashMap.isEmpty_eq_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : (m.insert a b).size = bif m.contains a then m.size else m.size + 1 :=
  DHashMap.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β} : m.size ≤ (m.insert a b).size :=
  DHashMap.size_le_size_insert

@[simp]
theorem remove_empty {a : α} {c : Nat} : (empty c : HashMap α β).remove a = empty c :=
  ext DHashMap.remove_empty

@[simp]
theorem remove_emptyc {a : α} : (∅ : HashMap α β).remove a = ∅ :=
  ext DHashMap.remove_emptyc

@[simp]
theorem isEmpty_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).isEmpty = (m.isEmpty || (m.size == 1 && m.contains a)) :=
  DHashMap.isEmpty_remove

@[simp]
theorem contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a = (!(k == a) && m.contains a) :=
  DHashMap.contains_remove

@[simp]
theorem mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k ↔ (k == a) = false ∧ a ∈ m :=
  DHashMap.mem_remove

theorem contains_of_contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a → m.contains a :=
  DHashMap.contains_of_contains_remove

theorem mem_of_mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k → a ∈ m :=
  DHashMap.mem_of_mem_remove

theorem size_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).size = bif m.contains a then m.size - 1 else m.size :=
  DHashMap.size_remove

theorem size_remove_le [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).size ≤ m.size :=
  DHashMap.size_remove_le

@[simp]
theorem fst_containsThenInsert {a : α} {b : β} : (m.containsThenInsert a b).1 = m.insert a b :=
  ext (DHashMap.fst_containsThenInsert)

@[simp]
theorem snd_containsThenInsert {a : α} {b : β} : (m.containsThenInsert a b).2 = m.contains a :=
  DHashMap.snd_containsThenInsert

@[simp]
theorem getElem?_empty {a : α} {c} : (empty c : HashMap α β)[a]? = none :=
  DHashMap.Const.get?_empty

@[simp]
theorem getElem?_emptyc {a : α} : (∅ : HashMap α β)[a]? = none :=
  DHashMap.Const.get?_emptyc

theorem getElem?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m[a]? = none :=
  DHashMap.Const.get?_of_isEmpty

theorem getElem?_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insert a b)[k]? = bif a == k then some b else m[k]? :=
  DHashMap.Const.get?_insert

@[simp]
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insert a b)[a]? = some b :=
  DHashMap.Const.get?_insert_self

theorem contains_eq_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = m[a]?.isSome :=
  DHashMap.Const.contains_eq_isSome_get?

theorem getElem?_remove [EquivBEq α] [LawfulHashable α] {a k : α} :
    (m.remove a)[k]? = bif a == k then none else m[k]? :=
  DHashMap.Const.get?_remove

@[simp]
theorem getElem?_remove_self [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a)[a]? = none :=
  DHashMap.Const.get?_remove_self

theorem getElem?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m[a]? = m[b]? :=
  DHashMap.Const.get?_congr hab

theorem getElem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    (m.insert a b)[k]'h₁ = if h₂ : a == k then b else m[k]'(mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  DHashMap.Const.get_insert (h₁ := h₁)

@[simp]
theorem getElem_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insert a b)[a]'mem_insert_self = b :=
  DHashMap.Const.get_insert_self

theorem getElem_remove [EquivBEq α] [LawfulHashable α] {a k : α} {h'} :
    (m.remove a)[k]'h' = m[k]'(mem_of_mem_remove h') :=
  DHashMap.Const.get_remove (h' := h')

theorem getElem?_eq_some_getElem [EquivBEq α] [LawfulHashable α] {a : α} {h' : a ∈ m} : m[a]? = some (m[a]'h') :=
  @DHashMap.Const.get?_eq_some_get _ _ _ _ _ _ _ _ h'

theorem getElem_congr [LawfulBEq α] {a b : α} (hab : a == b) {h'} : m[a]'h' = m[b]'((mem_congr hab).1 h') :=
  DHashMap.Const.get_congr hab (h' := h')

@[simp]
theorem getElem!_empty [Inhabited β] {a : α} {c} : (empty c : HashMap α β)[a]! = default :=
  DHashMap.Const.get!_empty

@[simp]
theorem getElem!_emptyc [Inhabited β] {a : α} : (∅ : HashMap α β)[a]! = default :=
  DHashMap.Const.get!_emptyc

theorem getElem!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m.isEmpty = true → m[a]! = default :=
  DHashMap.Const.get!_of_isEmpty

theorem getElem!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    (m.insert a b)[k]! = bif a == k then b else m[k]! :=
  DHashMap.Const.get!_insert

@[simp]
theorem getElem!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {b : β} :
    (m.insert a b)[a]! = b :=
  DHashMap.Const.get!_insert_self

theorem getElem!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = false → m[a]! = default :=
  DHashMap.Const.get!_eq_default_of_contains_eq_false

theorem getElem!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    ¬a ∈ m → m[a]! = default :=
  DHashMap.Const.get!_eq_default

theorem getElem!_remove [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} :
    (m.remove a)[k]! = bif a == k then default else m[k]! :=
  DHashMap.Const.get!_remove

@[simp]
theorem getElem!_remove_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    (m.remove k)[k]! = default :=
  DHashMap.Const.get!_remove_self

theorem getElem?_eq_some_getElem!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = true → m[a]? = some m[a]! :=
  DHashMap.Const.get?_eq_some_get!_of_contains

theorem getElem?_eq_some_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    a ∈ m → m[a]? = some m[a]! :=
  DHashMap.Const.get?_eq_some_get!

theorem getElem!_eq_get!_getElem? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m[a]?.get! :=
  DHashMap.Const.get!_eq_get!_get?

theorem getElem_eq_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h'} :
    m[a]'h' = m[a]! :=
  @DHashMap.Const.get_eq_get! _ _ _ _ _ _ _ _ _ h'

theorem getElem!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    m[a]! = m[b]! :=
  DHashMap.Const.get!_congr hab

@[simp]
theorem getD_empty {a : α} {fallback : β} {c} : (empty c : HashMap α β).getD a fallback = fallback :=
  DHashMap.Const.getD_empty

@[simp]
theorem getD_emptyc {a : α} {fallback : β} : (∅ : HashMap α β).getD a fallback = fallback :=
  DHashMap.Const.getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.isEmpty = true → m.getD a fallback = fallback :=
  DHashMap.Const.getD_of_isEmpty

theorem getD_insert [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    (m.insert a b).getD k fallback = bif a == k then b else m.getD k fallback :=
  DHashMap.Const.getD_insert

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {fallback b : β} :
   (m.insert a b).getD a fallback = b :=
  DHashMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = false → m.getD a fallback = fallback :=
  DHashMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  DHashMap.Const.getD_eq_fallback

theorem getD_remove [EquivBEq α] [LawfulHashable α] {a k : α} {fallback : β} :
    (m.remove a).getD k fallback = bif a == k then fallback else m.getD k fallback :=
  DHashMap.Const.getD_remove

@[simp]
theorem getD_remove_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    (m.remove k).getD k fallback = fallback :=
  DHashMap.Const.getD_remove_self

theorem getElem?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → m[a]? = some (m.getD a fallback) :=
  DHashMap.Const.get?_eq_some_getD_of_contains

theorem getElem?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    a ∈ m → m[a]? = some (m.getD a fallback) :=
  DHashMap.Const.get?_eq_some_getD

theorem getD_eq_getD_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.getD a fallback = m[a]?.getD fallback :=
  DHashMap.Const.getD_eq_getD_get?

theorem getElem_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h'} :
    m[a]'h' = m.getD a fallback :=
  @DHashMap.Const.get_eq_getD _ _ _ _ _ _ _ _ _ h'

theorem getElem!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m.getD a default :=
  DHashMap.Const.get!_eq_getD_default

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    m.getD a fallback = m.getD b fallback :=
  DHashMap.Const.getD_congr hab

@[simp]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insertIfNew a b).isEmpty = false :=
  DHashMap.isEmpty_insertIfNew

@[simp]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insertIfNew a b).contains k = (a == k || m.contains k) :=
  DHashMap.contains_insertIfNew

@[simp]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    k ∈ m.insertIfNew a b ↔ a == k ∨ k ∈ m :=
  DHashMap.mem_insertIfNew

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof obligation in the statement of
    `getElem_insertIfNew`. -/
theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insertIfNew a b).contains k → ¬((a == k) ∧ m.contains a = false) → m.contains k :=
  DHashMap.contains_of_contains_insertIfNew

/-- This is a restatement of `mem_insertIfNew` that is written to exactly match the proof obligation in the statement of
    `getElem_insertIfNew`. -/
theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    k ∈ m.insertIfNew a b → ¬((a == k) ∧ ¬a ∈ m) → k ∈ m :=
  DHashMap.mem_of_mem_insertIfNew

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    (m.insertIfNew a b).size = bif m.contains a then m.size else m.size + 1 :=
  DHashMap.size_insertIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    m.size ≤ (m.insertIfNew a b).size :=
  DHashMap.size_le_size_insertIfNew

theorem getElem?_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    (m.insertIfNew a b)[k]? = bif a == k && !m.contains a then some b else m[k]? :=
  DHashMap.Const.get?_insertIfNew

theorem getElem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    (m.insertIfNew a b)[k]'h₁ = if h₂ : a == k ∧ ¬a ∈ m then b else m[k]'(mem_of_mem_insertIfNew h₁ h₂) :=
  DHashMap.Const.get_insertIfNew (h₁ := h₁)

theorem getElem!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    (m.insertIfNew a b)[k]! = bif a == k && !m.contains a then b else m[k]! :=
  DHashMap.Const.get!_insertIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    (m.insertIfNew a b).getD k fallback = bif a == k && !m.contains a then b else m.getD k fallback :=
  DHashMap.Const.getD_insertIfNew

@[simp]
theorem fst_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).1 = m.insertIfNew a b :=
  ext (DHashMap.Const.fst_getThenInsertIfNew?)

@[simp]
theorem snd_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).2 = get? m a :=
  DHashMap.Const.snd_getThenInsertIfNew?

end

end MyLean.HashMap
