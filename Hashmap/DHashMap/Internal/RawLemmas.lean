/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Internal.WF

set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]

namespace MyLean.DHashMap

section empty

@[simp]
theorem Raw₀.buckets_empty {c} {i : Nat} {h} : (empty c : Raw₀ α β).1.buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem Raw.buckets_empty {c} {i : Nat} {h} : (empty c : Raw α β).buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem Raw.buckets_emptyc {i : Nat} {h} : (∅ : Raw α β).buckets[i]'h = AssocList.nil :=
  buckets_empty

@[simp]
theorem buckets_empty {c} {i : Nat} {h} : (empty c : DHashMap α β).1.buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem buckets_emptyc {i : Nat} {h} : (∅ : DHashMap α β).1.buckets[i]'h = AssocList.nil :=
  buckets_empty

end empty

namespace Raw₀

variable (m : Raw₀ α β) (h : m.1.WF)

macro "wf_trivial" : tactic => `(tactic|
  repeat (first | apply Raw.WFImp.insert | apply Raw.WFImp.remove | apply Raw.WF.out | assumption | apply wfImp_empty | apply Raw.WFImp.distinct))

macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean Elab Meta Tactic

def baseNames : MetaM (List (TSyntax `term)) := do
  return [ ← `(contains_eq_containsKey), ← `(Raw.isEmpty_eq_isEmpty), ← `(Raw.size_eq_length), ← `(get?_eq_getValueCast?),
    ← `(Const.get?_eq_getValue?), ← `(get_eq_getValueCast), ← `(Const.get_eq_getValue) ]

def modifyNames : MetaM (List (TSyntax `term)) := do
  return [← `(toListModel_insert), ← `(toListModel_remove) ]

def congrNames : MetaM (List (TSyntax `term)) := do
  return [← `(List.Perm.isEmpty_eq), ← `(List.containsKey_of_perm), ← `(List.Perm.length_eq),
    ← `(List.getValueCast?_of_perm _), ← `(List.getValue?_of_perm _), ← `(List.getValue_of_perm _),
    ← `(List.getValueCast_of_perm _) ]

syntax "simp_to_model" ("with" term)? ("using" term)? : tactic

elab_rules : tactic
| `(tactic| simp_to_model $[with $with?]? $[using $using?]?) => withMainContext do
  for name in ← baseNames do
    evalTactic (← `(tactic| repeat rw [$name:term]))
  for modify in ← modifyNames do
    for congr in ← congrNames do
      evalTactic (← `(tactic| repeat rw [$congr:term ($modify:term ..)]))
  if let some usingLem := using? then
    evalTactic (← `(tactic| apply $usingLem:term))
  if let some withLem := with? then
    evalTactic (← `(tactic| rw [$withLem:term]))
  for sideGoal in (← getUnsolvedGoals) do
    let _ ← evalTacticAt (← `(tactic| wf_trivial)) sideGoal
  return ()

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw₀ α β).1.isEmpty := by
  rw [Raw.isEmpty_eq_isEmpty wfImp_empty, toListModel_buckets_empty, List.isEmpty_nil]

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} : (m.insert a b).1.isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntry

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m.contains a = m.contains b := by
  simp_to_model using List.containsKey_eq_of_beq hab

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).contains a = false := by
  simp [contains]

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} : m.1.isEmpty = true → m.contains a = false := by
  simp_to_model; empty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] : m.1.isEmpty = false ↔ ∃ a, m.contains a = true := by
  simp only [contains_eq_containsKey h.out]
  simp_to_model using List.isEmpty_eq_false_iff_exists_containsKey

theorem contains_insert [EquivBEq α] [LawfulHashable α] (a k : α) (b : β a) : (m.insert a b).contains k = ((a == k) || m.contains k) := by
  simp_to_model using List.containsKey_insertEntry

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    (m.insert a b).contains k → (a == k) = false → m.contains k := by
  simp_to_model using List.containsKey_of_containsKey_insertEntry

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} : (m.insert a b).contains a := by
  simp_to_model using List.containsKey_insertEntry_self

@[simp]
theorem size_empty {c} : (empty c : Raw₀ α β).1.size = 0 := rfl

theorem isEmpty_eq_size_eq_zero : m.1.isEmpty = (m.1.size == 0) := by
  simp [Raw.isEmpty]

theorem size_insert [EquivBEq α] [LawfulHashable α] (a : α) (b : β a) : (m.insert a b).1.size = bif m.contains a then m.1.size else m.1.size + 1 := by
  simp_to_model using List.length_insertEntry

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (a : α) (b : β a) : m.1.size ≤ (m.insert a b).1.size := by
  simp_to_model using List.length_le_length_insert

@[simp]
theorem remove_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).remove a = empty c := by
  simp [remove, empty]

theorem isEmpty_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).1.isEmpty = (m.1.isEmpty || (m.1.size == 1 && m.contains a)) := by
  simp_to_model using List.isEmpty_removeKey

theorem contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a = (!(k == a) && m.contains a) := by
  simp_to_model using List.containsKey_removeKey

theorem contains_of_contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a → m.contains a := by
  simp_to_model using List.containsKey_of_containsKey_removeKey

theorem size_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).1.size = bif m.contains a then m.1.size - 1 else m.1.size := by
  simp_to_model using List.length_removeKey

theorem size_remove_le [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).1.size ≤ m.1.size := by
  simp_to_model using List.length_removeKey_le

@[simp]
theorem fst_containsThenInsert {a : α} {b : β a} : (m.containsThenInsert a b).1 = m.insert a b := by
  rw [containsThenInsert_eq_insertₘ, insert_eq_insertₘ]

@[simp]
theorem snd_containsThenInsert {a : α} {b : β a} : (m.containsThenInsert a b).2 = m.contains a := by
  rw [containsThenInsert_eq_containsₘ, contains_eq_containsₘ]

@[simp]
theorem get?_empty [LawfulBEq α] {a : α} {c} : (empty c : Raw₀ α β).get? a = none := by
  simp [get?]

theorem get?_of_isEmpty [LawfulBEq α] {a : α} : m.1.isEmpty = true → m.get? a = none := by
  simp_to_model; empty

theorem get?_insert [LawfulBEq α] {a k : α} {b : β a} :
    (m.insert a b).get? k = if h : a == k then some (cast (congrArg β (eq_of_beq h)) b) else m.get? k := by
  simp_to_model using List.getValueCast?_insertEntry

theorem get?_insert_self [LawfulBEq α] {a : α} {b : β a} : (m.insert a b).get? a = some b := by
  simp_to_model using List.getValueCast?_insertEntry_self

theorem contains_eq_isSome_get? [LawfulBEq α] {a : α} : m.contains a = (m.get? a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValueCast?

theorem get?_remove [LawfulBEq α] {a k : α} : (m.remove a).get? k = bif a == k then none else m.get? k := by
  simp_to_model using List.getValueCast?_removeKey

theorem get?_remove_self [LawfulBEq α] {a : α} : (m.remove a).get? a = none := by
  simp_to_model using List.getValueCast?_removeKey_self

namespace Const

variable {β : Type v} (m : DHashMap.Raw₀ α (fun _ => β)) (h : m.1.WF)

@[simp]
theorem get?_empty {a : α} {c} : get? (empty c : Raw₀ α (fun _ => β)) a = none := by
  simp [get?]

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} : m.1.isEmpty = true → get? m a = none := by
  simp_to_model; empty

theorem get?_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    get? (m.insert a b) k = bif a == k then some b else get? m k := by
  simp_to_model using List.getValue?_insertEntry

theorem get?_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    get? (m.insert a b) a = some b := by
  simp_to_model using List.getValue?_insertEntry_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = (get? m a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValue?

theorem get?_remove [EquivBEq α] [LawfulHashable α] {a k : α} :
    Const.get? (m.remove a) k = bif a == k then none else get? m k := by
  simp_to_model using List.getValue?_removeKey

theorem get?_remove_self [EquivBEq α] [LawfulHashable α] {a : α} : get? (m.remove a) a = none := by
  simp_to_model using List.getValue?_removeKey_self

theorem get?_eq_get? [LawfulBEq α] {a : α} : get? m a = m.get? a := by
  simp_to_model with List.getValueCast?_eq_getValue?

theorem get?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : get? m a = get? m b := by
  simp_to_model using List.getValue?_eq_of_beq

end Const

theorem get_insert [LawfulBEq α] {a k : α} {b : β a} {h₁} :
    (m.insert a b).get k h₁ =
      if h₂ : a == k then
        cast (congrArg β (eq_of_beq h₂)) b
      else
        m.get k (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model
  rw [List.getValueCast_insertEntry]
  split
  · rfl
  · simp_to_model

theorem get_insert_self [LawfulBEq α] {a : α} {b : β a} : (m.insert a b).get a (contains_insert_self _ h) = b := by
  simp_to_model using List.getValueCast_insertEntry_self

end Raw₀

end MyLean.DHashMap
