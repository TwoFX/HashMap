/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Internal.WF
import Lean.Elab.Command

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
  repeat (first | apply Raw.WFImp.insert | apply Raw.WFImp.insertIfNew | apply Raw.WFImp.remove | apply Raw.WF.out | assumption | apply wfImp_empty | apply Raw.WFImp.distinct | apply Raw.WF.empty₀))

macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean Elab Meta Tactic

def baseNames : MetaM (List (TSyntax `term)) := do
  return [ ← `(contains_eq_containsKey), ← `(Raw.isEmpty_eq_isEmpty), ← `(Raw.size_eq_length), ← `(get?_eq_getValueCast?),
    ← `(Const.get?_eq_getValue?), ← `(get_eq_getValueCast), ← `(Const.get_eq_getValue), ← `(get!_eq_getValueCast!),
    ← `(getD_eq_getValueCastD), ← `(Const.get!_eq_getValue!), ← `(Const.getD_eq_getValueD) ]

def modifyNames : List Name :=
  [ ``toListModel_insert, ``toListModel_remove, ``toListModel_insertIfNew ]

def congrNames : MetaM (List (TSyntax `term)) := do
  return [← `(MyLean.DHashMap.Internal.Perm.isEmpty_eq), ← `(List.containsKey_of_perm), ← `(MyLean.DHashMap.Internal.Perm.length_eq),
    ← `(List.getValueCast?_of_perm _), ← `(List.getValue?_of_perm _), ← `(List.getValue_of_perm _),
    ← `(List.getValueCast_of_perm _), ← `(List.getValueCast!_of_perm _), ← `(List.getValueCastD_of_perm _),
    ← `(List.getValue!_of_perm _), ← `(List.getValueD_of_perm _) ]

syntax "simp_to_model" ("with" term)? ("using" term)? : tactic

elab_rules : tactic
| `(tactic| simp_to_model $[with $with?]? $[using $using?]?) => withMainContext do
  for name in ← baseNames do
    evalTactic (← `(tactic| repeat simp (discharger := wf_trivial) only [$name:term]))
  for modify in modifyNames do
    for congr in ← congrNames do
      evalTactic (← `(tactic| repeat simp (discharger := wf_trivial) only [$congr:term ($(mkIdent modify) ..)]))
  if let some usingLem := using? then
    evalTactic (← `(tactic| apply $usingLem:term))
  if let some withLem := with? then
    evalTactic (← `(tactic| simp (discharger := wf_trivial) only [$withLem:term]))
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

theorem contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} : (m.insert a b).contains k = ((a == k) || m.contains k) := by
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

theorem size_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} : (m.insert a b).1.size = bif m.contains a then m.1.size else m.1.size + 1 := by
  simp_to_model using List.length_insertEntry

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} : m.1.size ≤ (m.insert a b).1.size := by
  simp_to_model using List.length_le_length_insertEntry

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

theorem get?_eq_none [LawfulBEq α] {a : α} : m.contains a = false → m.get? a = none := by
  simp_to_model using List.getValueCast?_eq_none

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

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = false → get? m a = none := by
  simp_to_model using List.getValue?_eq_none.2

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
  simp_to_model using List.getValueCast_insertEntry

theorem get_insert_self [LawfulBEq α] {a : α} {b : β a} : (m.insert a b).get a (contains_insert_self _ h) = b := by
  simp_to_model using List.getValueCast_insertEntry_self

theorem get_remove [LawfulBEq α] {a k : α} {h'} :
    (m.remove a).get k h' = m.get k (contains_of_contains_remove _ h h') := by
  simp_to_model using List.getValueCast_removeKey

theorem get?_eq_some_get [LawfulBEq α] {a : α} {h} : m.get? a = some (m.get a h) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCast

namespace Const

variable {β : Type v} (m : DHashMap.Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    get (m.insert a b) k h₁ = if h₂ : a == k then b else get m k (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model using List.getValue_insertEntry

theorem get_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    get (m.insert a b) a (contains_insert_self _ h) = b := by
  simp_to_model using List.getValue_insertEntry_self

theorem get_remove [EquivBEq α] [LawfulHashable α] {a k : α} {h'} :
    get (m.remove a) k h' = get m k (contains_of_contains_remove _ h h') := by
  simp_to_model using List.getValue_removeKey

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} {h} : get? m a = some (get m a h) := by
  simp_to_model using List.getValue?_eq_some_getValue

theorem get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h := by
  simp_to_model using List.getValue_eq_getValueCast

theorem get_congr [LawfulBEq α] {a b : α} (hab : a == b) {h'} : get m a h' = get m b ((contains_congr _ h hab).symm.trans h') := by
  simp_to_model using List.getValue_congr

end Const

theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] {c} : (empty c : Raw₀ α β).get! a = default := by
  simp [get!, empty]

theorem get!_of_isEmpty [LawfulBEq α] {a : α} [Inhabited (β a)] : m.1.isEmpty = true → m.get! a = default := by
  simp_to_model; empty

theorem get!_insert [LawfulBEq α] {a k : α} [Inhabited (β k)] {b : β a} :
    (m.insert a b).get! k = if h : a == k then cast (congrArg β (eq_of_beq h)) b else m.get! k := by
  simp_to_model using List.getValueCast!_insertEntry

theorem get!_insert_self [LawfulBEq α] {a : α} [Inhabited (β a)] {b : β a} :
    (m.insert a b).get! a = b := by
  simp_to_model using List.getValueCast!_insertEntry_self

theorem get!_eq_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default := by
  simp_to_model using List.getValueCast!_eq_default

theorem get!_remove [LawfulBEq α] {a k : α} [Inhabited (β k)] :
    (m.remove a).get! k = bif a == k then default else m.get! k := by
  simp_to_model using List.getValueCast!_removeKey

theorem get!_remove_self [LawfulBEq α] {k : α} [Inhabited (β k)] :
    (m.remove k).get! k = default := by
  simp_to_model using List.getValueCast!_removeKey_self

theorem get?_eq_some_get! [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCast!

theorem get!_eq_get!_get? [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! := by
  simp_to_model using List.getValueCast!_eq_getValueCast?

theorem get_eq_get! [LawfulBEq α] {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a := by
  simp_to_model using List.getValueCast_eq_getValueCast!

namespace Const

variable {β : Type v} (m : DHashMap.Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get!_empty [Inhabited β] {a : α} {c} : get! (empty c : Raw₀ α (fun _ => β)) a = default := by
  simp [get!, empty]

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m.1.isEmpty = true → get! m a = default := by
  simp_to_model; empty

theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    get! (m.insert a b) k = bif a == k then b else get! m k := by
  simp_to_model using List.getValue!_insertEntry

theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {b : β} :
    get! (m.insert a b) a = b := by
  simp_to_model using List.getValue!_insertEntry_self

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = false → get! m a = default := by
  simp_to_model using List.getValue!_eq_default

theorem get!_remove [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} :
    get! (m.remove a) k = bif a == k then default else get! m k := by
  simp_to_model using List.getValue!_removeKey

theorem get!_remove_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    get! (m.remove k) k = default := by
  simp_to_model using List.getValue!_removeKey_self

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = true → get? m a = some (get! m a) := by
  simp_to_model using List.getValue?_eq_some_getValue!

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = (get? m a).get! := by
  simp_to_model using List.getValue!_eq_getValue?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h} :
    get m a h = get! m a := by
  simp_to_model using List.getValue_eq_getValue!

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] {a : α} :
    get! m a = m.get! a := by
  simp_to_model using List.getValue!_eq_getValueCast!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    get! m a = get! m b := by
  simp_to_model using List.getValue!_congr

end Const

theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} {c} : (empty c : Raw₀ α β).getD a fallback = fallback := by
  simp [getD, empty]

theorem getD_of_isEmpty [LawfulBEq α] {a : α} {fallback : β a} : m.1.isEmpty = true → m.getD a fallback = fallback := by
  simp_to_model; empty

theorem getD_insert [LawfulBEq α] {a k : α} {fallback : β k} {b : β a} :
    (m.insert a b).getD k fallback = if h : a == k then cast (congrArg β (eq_of_beq h)) b else m.getD k fallback := by
  simp_to_model using List.getValueCastD_insertEntry

theorem getD_insert_self [LawfulBEq α] {a : α} {fallback b : β a} :
    (m.insert a b).getD a fallback = b := by
  simp_to_model using List.getValueCastD_insertEntry_self

theorem getD_eq_fallback [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback := by
  simp_to_model using List.getValueCastD_eq_fallback

theorem getD_remove [LawfulBEq α] {a k : α} {fallback : β k} :
    (m.remove a).getD k fallback = bif a == k then fallback else m.getD k fallback := by
  simp_to_model using List.getValueCastD_removeKey

theorem getD_remove_self [LawfulBEq α] {k : α} {fallback : β k} :
    (m.remove k).getD k fallback = fallback := by
  simp_to_model using List.getValueCastD_removeKey_self

theorem get?_eq_some_getD [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCastD

theorem getD_eq_getD_get? [LawfulBEq α] {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback := by
  simp_to_model using List.getValueCastD_eq_getValueCast?

theorem get_eq_getD [LawfulBEq α] {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback := by
  simp_to_model using List.getValueCast_eq_getValueCastD

theorem get!_eq_getD_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = m.getD a default := by
  simp_to_model using List.getValueCast!_eq_getValueCastD_default

namespace Const

variable {β : Type v} (m : DHashMap.Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem getD_empty {a : α} {fallback : β} {c} : getD (empty c : Raw₀ α (fun _ => β)) a fallback = fallback := by
  simp [getD, empty]

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.1.isEmpty = true → getD m a fallback = fallback := by
  simp_to_model; empty

theorem getD_insert [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    getD (m.insert a b) k fallback = bif a == k then b else getD m k fallback := by
  simp_to_model using List.getValueD_insertEntry

theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {fallback b : β} :
    getD (m.insert a b) a fallback = b := by
  simp_to_model using List.getValueD_insertEntry_self

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = false → getD m a fallback = fallback := by
  simp_to_model using List.getValueD_eq_fallback

theorem getD_remove [EquivBEq α] [LawfulHashable α] {a k : α} {fallback : β} :
    getD (m.remove a) k fallback = bif a == k then fallback else getD m k fallback := by
  simp_to_model using List.getValueD_removeKey

theorem getD_remove_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    getD (m.remove k) k fallback = fallback := by
  simp_to_model using List.getValueD_removeKey_self

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) := by
  simp_to_model using List.getValue?_eq_some_getValueD

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback := by
  simp_to_model using List.getValueD_eq_getValue?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback := by
  simp_to_model using List.getValue_eq_getValueD

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = getD m a default := by
  simp_to_model using List.getValue!_eq_getValueD_default

theorem getD_eq_getD [LawfulBEq α] {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback := by
  simp_to_model using List.getValueD_eq_getValueCastD

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    getD m a fallback = getD m b fallback := by
  simp_to_model using List.getValueD_congr

end Const

theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} :
    (m.insertIfNew a b).1.isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntryIfNew

theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    (m.insertIfNew a b).contains k = (a == k || m.contains k) := by
  simp_to_model using List.containsKey_insertEntryIfNew

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof obligation in the statement of
    `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    (m.insertIfNew a b).contains k → ¬((a == k) ∧ m.contains a = false) → m.contains k := by
  simp_to_model using List.containsKey_of_containsKey_insertEntryIfNew

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} :
    (m.insertIfNew a b).1.size = bif m.contains a then m.1.size else m.1.size + 1 := by
  simp_to_model using List.length_insertEntryIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} :
    m.1.size ≤ (m.insertIfNew a b).1.size := by
  simp_to_model using List.length_le_length_insertEntryIfNew

theorem get?_insertIfNew [LawfulBEq α] {a k : α} {b : β a} :
    (m.insertIfNew a b).get? k = if h : a == k ∧ m.contains a = false then some (cast (congrArg β (eq_of_beq h.1)) b) else m.get? k := by
  simp_to_model using List.getValueCast?_insertEntryIfNew

theorem get_insertIfNew [LawfulBEq α] {a k : α} {b : β a} {h₁} :
    (m.insertIfNew a b).get k h₁ = if h₂ : a == k ∧ m.contains a = false then cast (congrArg β (eq_of_beq h₂.1)) b else m.get k
      (contains_of_contains_insertIfNew _ h h₁ h₂) := by
  simp_to_model using List.getValueCast_insertEntryIfNew

theorem get!_insertIfNew [LawfulBEq α] {a k : α} [Inhabited (β k)] {b : β a} :
    (m.insertIfNew a b).get! k = if h : a == k ∧ m.contains a = false then cast (congrArg β (eq_of_beq h.1)) b else m.get! k := by
  simp_to_model using List.getValueCast!_insertEntryIfNew

theorem getD_insertIfNew [LawfulBEq α] {a k : α} {fallback : β k} {b : β a} :
    (m.insertIfNew a b).getD k fallback = if h : a == k ∧ m.contains a = false then cast (congrArg β (eq_of_beq h.1)) b else m.getD k fallback := by
  simp_to_model using List.getValueCastD_insertEntryIfNew

namespace Const

variable {β : Type v} (m : DHashMap.Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    get? (m.insertIfNew a b) k = bif a == k && !m.contains a then some b else get? m k := by
  simp_to_model using List.getValue?_insertEntryIfNew

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    get (m.insertIfNew a b) k h₁ = if h₂ : a == k ∧ m.contains a = false then b else get m k (contains_of_contains_insertIfNew _ h h₁ h₂) := by
  simp_to_model using List.getValue_insertEntryIfNew

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    get! (m.insertIfNew a b) k = bif a == k && !m.contains a then b else get! m k := by
  simp_to_model using List.getValue!_insertEntryIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    getD (m.insertIfNew a b) k fallback = bif a == k && !m.contains a then b else getD m k fallback := by
  simp_to_model using List.getValueD_insertEntryIfNew

end Const

@[simp]
theorem fst_getThenInsertIfNew? [LawfulBEq α] {a : α} {b : β a} : (m.getThenInsertIfNew? a b).1 = m.insertIfNew a b := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ, insertIfNew_eq_insertIfNewₘ]

@[simp]
theorem snd_getThenInsertIfNew? [LawfulBEq α] {a : α} {b : β a} : (m.getThenInsertIfNew? a b).2 = m.get? a := by
  rw [getThenInsertIfNew?_eq_get?ₘ, get?_eq_get?ₘ]

namespace Const

variable {β : Type v} (m : DHashMap.Raw₀ α (fun _ => β)) (h : m.1.WF)

@[simp]
theorem fst_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).1 = m.insertIfNew a b := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ, insertIfNew_eq_insertIfNewₘ]

@[simp]
theorem snd_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).2 = get? m a := by
  rw [getThenInsertIfNew?_eq_get?ₘ, get?_eq_get?ₘ]

end Const

end Raw₀

end MyLean.DHashMap
