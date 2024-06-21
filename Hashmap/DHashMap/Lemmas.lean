/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Internal.RawLemmas

set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace MyLean.DHashMap

namespace Raw

variable (m : Raw α β) (h : m.WF)

section

open Lean Elab Meta Tactic

syntax "simp_to_raw" ("using" term)? : tactic

def baseNames : List Name :=
  [
    ``empty_eq, ``emptyc_eq,
    ``insert_eq, ``insert_val,
    ``insertIfNew_eq, ``insertIfNew_val,
    ``snd_containsThenInsert_eq, ``snd_containsThenInsert_val,
    ``snd_getThenInsertIfNew?_eq, ``snd_getThenInsertIfNew?_val,
    ``map_eq, ``map_val,
    ``filter_eq, ``filter_val,
    ``remove_eq, ``remove_val,
    ``filterMap_eq, ``filterMap_val,
    ``Const.snd_getThenInsertIfNew?_eq, ``Const.snd_getThenInsertIfNew?_val,
    ``fst_containsThenInsert_eq, ``fst_containsThenInsert_val,
    ``Const.get?_eq, ``Const.get?_val,
    ``Const.get_eq, ``Const.get_val,
    ``Const.getD_eq, ``Const.getD_val,
    ``Const.get!_eq, ``Const.get!_val,
    ``fst_getThenInsertIfNew?_eq, ``fst_getThenInsertIfNew?_val,
    ``Const.fst_getThenInsertIfNew?_eq, ``Const.fst_getThenInsertIfNew?_val,
    ``get?_eq, ``get?_val,
    ``contains_eq, ``contains_val,
    ``get_eq, ``get_val,
    ``getD_eq, ``getD_val,
    ``get!_eq, ``get!_val
    ]

elab_rules : tactic
| `(tactic| simp_to_raw $[using $using?]?) => withMainContext do
  for name in baseNames do
    -- TODO: change this into a single simp invocation
    evalTactic (← `(tactic| try simp (discharger := wf_trivial) only [$(mkIdent name):term]))
  if let some usingLem := using? then
    evalTactic (← `(tactic| apply $usingLem:term))
  for sideGoal in (← getUnsolvedGoals) do
    let _ ← evalTacticAt (← `(tactic| wf_trivial)) sideGoal
  return ()

end

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α β).isEmpty := by
  simp_to_raw using Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} : (m.insert a b).isEmpty = false := by
  simp_to_raw using Raw₀.isEmpty_insert

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m.contains a = m.contains b := by
  simp_to_raw using Raw₀.contains_congr

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m := by
  simp [mem_iff_contains, contains_congr _ h hab]

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α β).contains a = false := by
  simp_to_raw using Raw₀.contains_empty

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α β) := by
  simp [mem_iff_contains]

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false :=
  contains_empty

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α β) :=
  not_mem_empty

theorem contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} : (m.insert a b).contains k = (a == k || m.contains k) := by
  simp_to_raw using Raw₀.contains_insert

theorem mem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} : k ∈ m.insert a b ↔ a == k ∨ k ∈ m := by
  simp [mem_iff_contains, contains_insert m h]

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    (m.insert a b).contains k → (a == k) = false → m.contains k := by
  simp_to_raw using Raw₀.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    k ∈ m.insert a b → (a == k) = false → k ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_insert m h

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} : (m.insert a b).contains a := by
  simp_to_raw using Raw₀.contains_insert_self

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} : a ∈ m.insert a b := by
  simp [mem_iff_contains, contains_insert_self m h]

theorem size_empty {c} : (empty c : Raw α β).size = 0 := by
  simp_to_raw using Raw₀.size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) := by
  simp [isEmpty]

theorem size_insert [EquivBEq α] [LawfulHashable α] (a : α) (b : β a) : (m.insert a b).size = bif m.contains a then m.size else m.size + 1 := by
  simp_to_raw using Raw₀.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (a : α) (b : β a) : m.size ≤ (m.insert a b).size := by
  simp_to_raw using Raw₀.size_le_size_insert ⟨m, _⟩ h

@[simp]
theorem remove_empty {a : α} {c : Nat} : (empty c : Raw α β).remove a = empty c := by
  rw [remove_eq (by wf_trivial)]
  exact congrArg Subtype.val Raw₀.remove_empty

@[simp]
theorem remove_emptyc {a : α} : (∅ : Raw α β).remove a = ∅ :=
  remove_empty

theorem isEmpty_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).isEmpty = (m.isEmpty || (m.size == 1 && m.contains a)) := by
  simp_to_raw using Raw₀.isEmpty_remove

theorem contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a = (!(k == a) && m.contains a) := by
  simp_to_raw using Raw₀.contains_remove

theorem mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k ↔ (k == a) = false ∧ a ∈ m := by
  simp [mem_iff_contains, contains_remove m h]

theorem contains_of_contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} : (m.remove k).contains a → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_remove

theorem size_remove [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).size = bif m.contains a then m.size - 1 else m.size := by
  simp_to_raw using Raw₀.size_remove

theorem size_remove_le [EquivBEq α] [LawfulHashable α] {a : α} : (m.remove a).size ≤ m.size := by
  simp_to_raw using Raw₀.size_remove_le

@[simp]
theorem fst_containsThenInsert {a : α} {b : β a} : (m.containsThenInsert a b).1 = m.insert a b := by
  simp_to_raw using congrArg Subtype.val (Raw₀.fst_containsThenInsert _)

@[simp]
theorem snd_containsThenInsert {a : α} {b : β a} : (m.containsThenInsert a b).2 = m.contains a := by
  simp_to_raw using Raw₀.snd_containsThenInsert

@[simp]
theorem get?_empty [LawfulBEq α] {a : α} {c} : (empty c : Raw α β).get? a = none := by
  simp_to_raw using Raw₀.get?_empty

theorem get?_of_isEmpty [LawfulBEq α] {a : α} : m.isEmpty = true → m.get? a = none := by
  simp_to_raw using Raw₀.get?_of_isEmpty ⟨m, _⟩

theorem get?_insert [LawfulBEq α] {a k : α} {b : β a} :
    (m.insert a b).get? k = if h : a == k then some (cast (congrArg β (eq_of_beq h)) b) else m.get? k := by
  simp_to_raw using Raw₀.get?_insert

theorem get?_insert_self [LawfulBEq α] {a : α} {b : β a} : (m.insert a b).get? a = some b := by
  simp_to_raw using Raw₀.get?_insert_self

theorem contains_eq_isSome_get? [LawfulBEq α] {a : α} : m.contains a = (m.get? a).isSome := by
  simp_to_raw using Raw₀.contains_eq_isSome_get?

theorem get?_remove [LawfulBEq α] {a k : α} : (m.remove a).get? k = bif a == k then none else m.get? k := by
  simp_to_raw using Raw₀.get?_remove

theorem get?_remove_self [LawfulBEq α] {a : α} : (m.remove a).get? a = none := by
  simp_to_raw using Raw₀.get?_remove_self

namespace Const

variable {β : Type v} (m : DHashMap.Raw α (fun _ => β)) (h : m.WF)

@[simp]
theorem get?_empty {a : α} {c} : get? (empty c : Raw α (fun _ => β)) a = none := by
  simp_to_raw using Raw₀.Const.get?_empty

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → get? m a = none := by
  simp_to_raw using Raw₀.Const.get?_of_isEmpty ⟨m, _⟩

theorem get?_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    get? (m.insert a b) k = bif a == k then some b else get? m k := by
  simp_to_raw using Raw₀.Const.get?_insert

theorem get?_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    get? (m.insert a b) a = some b := by
  simp_to_raw using Raw₀.Const.get?_insert_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = (get? m a).isSome := by
  simp_to_raw using Raw₀.Const.contains_eq_isSome_get?

theorem get?_remove [EquivBEq α] [LawfulHashable α] {a k : α} :
    Const.get? (m.remove a) k = bif a == k then none else get? m k := by
  simp_to_raw using Raw₀.Const.get?_remove

theorem get?_remove_self [EquivBEq α] [LawfulHashable α] {a : α} : get? (m.remove a) a = none := by
  simp_to_raw using Raw₀.Const.get?_remove_self

theorem get?_eq_get? [LawfulBEq α] {a : α} : get? m a = m.get? a := by
  simp_to_raw using Raw₀.Const.get?_eq_get?

theorem get?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : get? m a = get? m b := by
  simp_to_raw using Raw₀.Const.get?_congr

end Const

theorem get_insert [LawfulBEq α] {a k : α} {b : β a} {h₁} :
    (m.insert a b).get k h₁ =
      if h₂ : a == k then
        cast (congrArg β (eq_of_beq h₂)) b
      else
        m.get k (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_raw using Raw₀.get_insert ⟨m, _⟩

theorem get_insert_self [LawfulBEq α] {a : α} {b : β a} : (m.insert a b).get a (contains_insert_self _ h) = b := by
  simp_to_raw using Raw₀.get_insert_self ⟨m, _⟩

theorem get_remove [LawfulBEq α] {a k : α} {h'} :
    (m.remove a).get k h' = m.get k (contains_of_contains_remove _ h h') := by
  simp_to_raw using Raw₀.get_remove ⟨m, _⟩

theorem get?_eq_some_get [LawfulBEq α] {a : α} {h} : m.get? a = some (m.get a h) := by
  simp_to_raw using Raw₀.get?_eq_some_get

namespace Const

variable {β : Type v} (m : DHashMap.Raw α (fun _ => β)) (h : m.WF)

theorem get_insert [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    get (m.insert a b) k h₁ = if h₂ : a == k then b else get m k (mem_of_mem_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_raw using Raw₀.Const.get_insert ⟨m, _⟩

theorem get_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {b : β} :
    get (m.insert a b) a (contains_insert_self _ h) = b := by
  simp_to_raw using Raw₀.Const.get_insert_self ⟨m, _⟩

theorem get_remove [EquivBEq α] [LawfulHashable α] {a k : α} {h'} :
    get (m.remove a) k h' = get m k (contains_of_contains_remove _ h h') := by
  simp_to_raw using Raw₀.Const.get_remove ⟨m, _⟩

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} {h} : get? m a = some (get m a h) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_get

theorem get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h := by
  simp_to_raw using Raw₀.Const.get_eq_get

theorem get_congr [LawfulBEq α] {a b : α} (hab : a == b) {h'} : get m a h' = get m b ((contains_congr _ h hab).symm.trans h') := by
  simp_to_raw using Raw₀.Const.get_congr

end Const

theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] {c} : (empty c : Raw α β).get! a = default := by
  simp_to_raw using Raw₀.get!_empty

theorem get!_of_isEmpty [LawfulBEq α] {a : α} [Inhabited (β a)] : m.isEmpty = true → m.get! a = default := by
  simp_to_raw using Raw₀.get!_of_isEmpty ⟨m, _⟩

theorem get!_insert [LawfulBEq α] {a k : α} [Inhabited (β k)] {b : β a} :
    (m.insert a b).get! k = if h : a == k then cast (congrArg β (eq_of_beq h)) b else m.get! k := by
  simp_to_raw using Raw₀.get!_insert

theorem get!_insert_self [LawfulBEq α] {a : α} [Inhabited (β a)] {b : β a} :
    (m.insert a b).get! a = b := by
  simp_to_raw using Raw₀.get!_insert_self

theorem get!_eq_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default := by
  simp_to_raw using Raw₀.get!_eq_default

theorem get!_remove [LawfulBEq α] {a k : α} [Inhabited (β k)] :
    (m.remove a).get! k = bif a == k then default else m.get! k := by
  simp_to_raw using Raw₀.get!_remove

theorem get!_remove_self [LawfulBEq α] {k : α} [Inhabited (β k)] :
    (m.remove k).get! k = default := by
  simp_to_raw using Raw₀.get!_remove_self

theorem get?_eq_some_get! [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) := by
  simp_to_raw using Raw₀.get?_eq_some_get!

theorem get!_eq_get!_get? [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! := by
  simp_to_raw using Raw₀.get!_eq_get!_get?

theorem get_eq_get! [LawfulBEq α] {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a := by
  simp_to_raw using Raw₀.get_eq_get!

namespace Const

variable {β : Type v} (m : DHashMap.Raw α (fun _ => β)) (h : m.WF)

theorem get!_empty [Inhabited β] {a : α} {c} : get! (empty c : Raw α (fun _ => β)) a = default := by
  simp_to_raw using Raw₀.Const.get!_empty

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m.isEmpty = true → get! m a = default := by
  simp_to_raw using Raw₀.Const.get!_of_isEmpty ⟨m, _⟩

theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    get! (m.insert a b) k = bif a == k then b else get! m k := by
  simp_to_raw using Raw₀.Const.get!_insert

theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {b : β} :
    get! (m.insert a b) a = b := by
  simp_to_raw using Raw₀.Const.get!_insert_self

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = false → get! m a = default := by
  simp_to_raw using Raw₀.Const.get!_eq_default

theorem get!_remove [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} :
    get! (m.remove a) k = bif a == k then default else get! m k := by
  simp_to_raw using Raw₀.Const.get!_remove

theorem get!_remove_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    get! (m.remove k) k = default := by
  simp_to_raw using Raw₀.Const.get!_remove_self

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = true → get? m a = some (get! m a) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_get!

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = (get? m a).get! := by
  simp_to_raw using Raw₀.Const.get!_eq_get!_get?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h} :
    get m a h = get! m a := by
  simp_to_raw using Raw₀.Const.get_eq_get!

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] {a : α} :
    get! m a = m.get! a := by
  simp_to_raw using Raw₀.Const.get!_eq_get!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    get! m a = get! m b := by
  simp_to_raw using Raw₀.Const.get!_congr

end Const

theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} {c} : (empty c : Raw α β).getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_empty

theorem getD_of_isEmpty [LawfulBEq α] {a : α} {fallback : β a} : m.isEmpty = true → m.getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_of_isEmpty ⟨m, _⟩

theorem getD_insert [LawfulBEq α] {a k : α} {fallback : β k} {b : β a} :
    (m.insert a b).getD k fallback = if h : a == k then cast (congrArg β (eq_of_beq h)) b else m.getD k fallback := by
  simp_to_raw using Raw₀.getD_insert

theorem getD_insert_self [LawfulBEq α] {a : α} {fallback b : β a} :
    (m.insert a b).getD a fallback = b := by
  simp_to_raw using Raw₀.getD_insert_self

theorem getD_eq_fallback [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_eq_fallback

theorem getD_remove [LawfulBEq α] {a k : α} {fallback : β k} :
    (m.remove a).getD k fallback = bif a == k then fallback else m.getD k fallback := by
  simp_to_raw using Raw₀.getD_remove

theorem getD_remove_self [LawfulBEq α] {k : α} {fallback : β k} :
    (m.remove k).getD k fallback = fallback := by
  simp_to_raw using Raw₀.getD_remove_self

theorem get?_eq_some_getD [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) := by
  simp_to_raw using Raw₀.get?_eq_some_getD

theorem getD_eq_getD_get? [LawfulBEq α] {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback := by
  simp_to_raw using Raw₀.getD_eq_getD_get?

theorem get_eq_getD [LawfulBEq α] {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback := by
  simp_to_raw using Raw₀.get_eq_getD

theorem get!_eq_getD_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = m.getD a default := by
  simp_to_raw using Raw₀.get!_eq_getD_default

namespace Const

variable {β : Type v} (m : DHashMap.Raw α (fun _ => β)) (h : m.WF)

theorem getD_empty {a : α} {fallback : β} {c} : getD (empty c : Raw α (fun _ => β)) a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.isEmpty = true → getD m a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_of_isEmpty ⟨m, _⟩

theorem getD_insert [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    getD (m.insert a b) k fallback = bif a == k then b else getD m k fallback := by
  simp_to_raw using Raw₀.Const.getD_insert

theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {a : α} {fallback b : β} :
   getD (m.insert a b) a fallback = b := by
  simp_to_raw using Raw₀.Const.getD_insert_self

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = false → getD m a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_fallback

theorem getD_remove [EquivBEq α] [LawfulHashable α] {a k : α} {fallback : β} :
    getD (m.remove a) k fallback = bif a == k then fallback else getD m k fallback := by
  simp_to_raw using Raw₀.Const.getD_remove

theorem getD_remove_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    getD (m.remove k) k fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_remove_self

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_getD

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_getD_get?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback := by
  simp_to_raw using Raw₀.Const.get_eq_getD

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = getD m a default := by
  simp_to_raw using Raw₀.Const.get!_eq_getD_default

theorem getD_eq_getD [LawfulBEq α] {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_getD

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    getD m a fallback = getD m b fallback := by
  simp_to_raw using Raw₀.Const.getD_congr

end Const

theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} :
    (m.insertIfNew a b).isEmpty = false := by
  simp_to_raw using Raw₀.isEmpty_insertIfNew

theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    (m.insertIfNew a b).contains k = (a == k || m.contains k) := by
  simp_to_raw using Raw₀.contains_insertIfNew

theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    k ∈ m.insertIfNew a b ↔ a == k ∨ k ∈ m := by
  simp [mem_iff_contains, contains_insertIfNew _ h]

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof obligation in the statement of
    `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    (m.insertIfNew a b).contains k → ¬((a == k) ∧ m.contains a = false) → m.contains k := by
  simp_to_raw using Raw₀.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β a} :
    k ∈ m.insertIfNew a b → ¬((a == k) ∧ ¬a ∈ m) → k ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew _ h

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} :
    (m.insertIfNew a b).size = bif m.contains a then m.size else m.size + 1 := by
  simp_to_raw using Raw₀.size_insertIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {a : α} {b : β a} :
    m.size ≤ (m.insertIfNew a b).size := by
  simp_to_raw using Raw₀.size_le_size_insertIfNew ⟨m, _⟩

theorem get?_insertIfNew [LawfulBEq α] {a k : α} {b : β a} :
    (m.insertIfNew a b).get? k = if h : a == k ∧ ¬a ∈ m then some (cast (congrArg β (eq_of_beq h.1)) b) else m.get? k := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get?_insertIfNew ⟨m, _⟩

theorem get_insertIfNew [LawfulBEq α] {a k : α} {b : β a} {h₁} :
    (m.insertIfNew a b).get k h₁ = if h₂ : a == k ∧ ¬a ∈ m then cast (congrArg β (eq_of_beq h₂.1)) b else m.get k
      (mem_of_mem_insertIfNew _ h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get_insertIfNew ⟨m, _⟩

theorem get!_insertIfNew [LawfulBEq α] {a k : α} [Inhabited (β k)] {b : β a} :
    (m.insertIfNew a b).get! k = if h : a == k ∧ ¬a ∈ m then cast (congrArg β (eq_of_beq h.1)) b else m.get! k := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get!_insertIfNew ⟨m, _⟩

theorem getD_insertIfNew [LawfulBEq α] {a k : α} {fallback : β k} {b : β a} :
    (m.insertIfNew a b).getD k fallback = if h : a == k ∧ ¬a ∈ m then cast (congrArg β (eq_of_beq h.1)) b else m.getD k fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.getD_insertIfNew

namespace Const

variable {β : Type v} (m : DHashMap.Raw α (fun _ => β)) (h : m.WF)

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} :
    get? (m.insertIfNew a b) k = bif a == k && !m.contains a then some b else get? m k := by
  simp_to_raw using Raw₀.Const.get?_insertIfNew

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {b : β} {h₁} :
    get (m.insertIfNew a b) k h₁ = if h₂ : a == k ∧ ¬a ∈ m then b else get m k (mem_of_mem_insertIfNew _ h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.get_insertIfNew ⟨m, _⟩

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {a k : α} {b : β} :
    get! (m.insertIfNew a b) k = bif a == k && !m.contains a then b else get! m k := by
  simp_to_raw using Raw₀.Const.get!_insertIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {a k : α} {fallback b : β} :
    getD (m.insertIfNew a b) k fallback = bif a == k && !m.contains a then b else getD m k fallback := by
  simp_to_raw using Raw₀.Const.getD_insertIfNew

end Const

@[simp]
theorem fst_getThenInsertIfNew? [LawfulBEq α] {a : α} {b : β a} : (m.getThenInsertIfNew? a b).1 = m.insertIfNew a b := by
  simp_to_raw using congrArg Subtype.val (Raw₀.fst_getThenInsertIfNew? _)

@[simp]
theorem snd_getThenInsertIfNew? [LawfulBEq α] {a : α} {b : β a} : (m.getThenInsertIfNew? a b).2 = m.get? a := by
  simp_to_raw using Raw₀.snd_getThenInsertIfNew?

namespace Const

variable {β : Type v} (m : DHashMap.Raw₀ α (fun _ => β)) (h : m.1.WF)

@[simp]
theorem fst_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).1 = m.insertIfNew a b := by
  simp_to_raw using congrArg Subtype.val (Raw₀.Const.fst_getThenInsertIfNew? _)

@[simp]
theorem snd_getThenInsertIfNew? {a : α} {b : β} : (getThenInsertIfNew? m a b).2 = get? m a := by
  simp_to_raw using Raw₀.Const.snd_getThenInsertIfNew?

end Const

end Raw
section

variable (m : DHashMap α β)

@[simp]
theorem Const.get?_empty {β : Type v} {a : α} {c : Nat} : Const.get? (empty c : DHashMap α (fun _ => β)) a = none :=
  Raw₀.Const.get?_empty

@[simp]
theorem Const.get?_emptyc {β : Type v} {a : α} : Const.get? (∅ : DHashMap α (fun _ => β)) a = none :=
  Raw₀.Const.get?_empty

end

end MyLean.DHashMap
