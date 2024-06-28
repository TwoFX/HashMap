/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

namespace Std.DHashMap.Internal

namespace Raw

theorem empty_eq [BEq α] [Hashable α] {c : Nat} : (Raw.empty c : Raw α β) = (Raw₀.empty c).1 := rfl

theorem emptyc_eq [BEq α] [Hashable α] : (∅ : Raw α β) = Raw₀.empty.1 := rfl

theorem insert_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    m.insert a b = (Raw₀.insert ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.insert, h.size_buckets_pos]

theorem insert_val [BEq α] [Hashable α] {m : Raw₀ α β} {a : α} {b : β a} :
    m.val.insert a b = m.insert a b := by
  simp [Raw.insert, m.2]

theorem insertIfNew_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    m.insertIfNew a b = (Raw₀.insertIfNew ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.insertIfNew, h.size_buckets_pos]

theorem insertIfNew_val [BEq α] [Hashable α] {m : Raw₀ α β} {a : α} {b : β a} :
    m.val.insertIfNew a b = m.insertIfNew a b := by
  simp [Raw.insertIfNew, m.2]

theorem fst_containsThenInsert_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.containsThenInsert a b).1 = (Raw₀.containsThenInsert ⟨m, h.size_buckets_pos⟩ a b).1.1 := by
  simp [Raw.containsThenInsert, h.size_buckets_pos]

theorem fst_containsThenInsert_val [BEq α] [Hashable α] {m : Raw₀ α β} {a : α} {b : β a} :
    (m.val.containsThenInsert a b).1 = (m.containsThenInsert a b).1.1 := by
  simp [Raw.containsThenInsert, m.2]

theorem snd_containsThenInsert_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.containsThenInsert a b).2 = (Raw₀.containsThenInsert ⟨m, h.size_buckets_pos⟩ a b).2 := by
  simp [Raw.containsThenInsert, h.size_buckets_pos]

theorem snd_containsThenInsert_val [BEq α] [Hashable α] {m : Raw₀ α β} {a : α} {b : β a} :
    (m.val.containsThenInsert a b).2 = (m.containsThenInsert a b).2 := by
  simp [Raw.containsThenInsert, m.2]

theorem fst_getThenInsertIfNew?_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.getThenInsertIfNew? a b).1 = (Raw₀.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).1.1 := by
  simp [Raw.getThenInsertIfNew?, h.size_buckets_pos]

theorem fst_getThenInsertIfNew?_val [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {b : β a} :
    (m.val.getThenInsertIfNew? a b).1 = (m.getThenInsertIfNew? a b).1.1 := by
  simp [Raw.getThenInsertIfNew?, m.2]

theorem snd_getThenInsertIfNew?_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.getThenInsertIfNew? a b).2 = (Raw₀.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).2 := by
  simp [Raw.getThenInsertIfNew?, h.size_buckets_pos]

theorem snd_getThenInsertIfNew?_val [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {b : β a} :
    (m.val.getThenInsertIfNew? a b).2 = (m.getThenInsertIfNew? a b).2 := by
  simp [Raw.getThenInsertIfNew?, m.2]

theorem get?_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} :
    m.get? a = Raw₀.get? ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.get?, h.size_buckets_pos]

theorem get?_val [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} :
    m.val.get? a = m.get? a := by
  simp [Raw.get?, m.2]

theorem contains_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} :
    m.contains a = Raw₀.contains ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.contains, h.size_buckets_pos]

theorem contains_val [BEq α] [Hashable α] {m : Raw₀ α β} {a : α} :
    m.val.contains a = m.contains a := by
  simp [Raw.contains, m.2]

theorem get_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {a : α} {h : a ∈ m} :
    m.get a h = Raw₀.get ⟨m, by rw [Raw.mem_iff_contains, Raw.contains] at h; split at h <;> simp_all⟩ a (by rw [Raw.mem_iff_contains, Raw.contains] at h; split at h <;> simp_all) := rfl

theorem get_val [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {h : a ∈ m.val} :
    m.val.get a h = m.get a (contains_val (m := m) ▸ h) := rfl

theorem getD_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} {fallback : β a} :
    m.getD a fallback = Raw₀.getD ⟨m, h.size_buckets_pos⟩ a fallback := by
  simp [Raw.getD, h.size_buckets_pos]

theorem getD_val [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {fallback : β a} :
    m.val.getD a fallback = m.getD a fallback := by
  simp [Raw.getD, m.2]

theorem get!_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} [Inhabited (β a)] :
    m.get! a = Raw₀.get! ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.get!, h.size_buckets_pos]

theorem get!_val [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} [Inhabited (β a)] :
    m.val.get! a = m.get! a := by
  simp [Raw.get!, m.2]

theorem remove_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} :
    m.remove a = Raw₀.remove ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.remove, h.size_buckets_pos]

theorem remove_val [BEq α] [Hashable α] {m : Raw₀ α β} {a : α} :
    m.val.remove a = m.remove a := by
  simp [Raw.remove, m.2]

theorem filterMap_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → Option (δ a)} :
    m.filterMap f = Raw₀.filterMap f ⟨m, h.size_buckets_pos⟩ := by
  simp [Raw.filterMap, h.size_buckets_pos]

theorem filterMap_val [BEq α] [Hashable α] {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} :
    m.val.filterMap f = m.filterMap f := by
  simp [Raw.filterMap, m.2]

theorem map_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → δ a} :
    m.map f = Raw₀.map f ⟨m, h.size_buckets_pos⟩ := by
  simp [Raw.map, h.size_buckets_pos]

theorem map_val [BEq α] [Hashable α] {m : Raw₀ α β} {f : (a : α) → β a → δ a} :
    m.val.map f = m.map f := by
  simp [Raw.map, m.2]

theorem filter_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → Bool} :
    m.filter f = Raw₀.filter f ⟨m, h.size_buckets_pos⟩ := by
  simp [Raw.filter, h.size_buckets_pos]

theorem filter_val [BEq α] [Hashable α] {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    m.val.filter f = m.filter f := by
  simp [Raw.filter, m.2]

section

variable {β : Type v}

theorem Const.get?_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} :
    Raw.Const.get? m a = Raw₀.Const.get? ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.Const.get?, h.size_buckets_pos]

theorem Const.get?_val [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)} {a : α} :
    Raw.Const.get? m.val a = Raw₀.Const.get? m a := by
  simp [Raw.Const.get?, m.2]

theorem Const.get_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {a : α} {h : a ∈ m} :
    Raw.Const.get m a h = Raw₀.Const.get ⟨m, by rw [Raw.mem_iff_contains, Raw.contains] at h; split at h <;> simp_all⟩ a (by rw [Raw.mem_iff_contains, Raw.contains] at h; split at h <;> simp_all) :=
  rfl

theorem Const.get_val [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)} {a : α} {h : a ∈ m.val} :
    Raw.Const.get m.val a h = Raw₀.Const.get m a (contains_val (m := m) ▸ h) := rfl

theorem Const.getD_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {fallback : β} :
    Raw.Const.getD m a fallback = Raw₀.Const.getD ⟨m, h.size_buckets_pos⟩ a fallback := by
  simp [Raw.Const.getD, h.size_buckets_pos]

theorem Const.getD_val [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)} {a : α} {fallback : β} :
    Raw.Const.getD m.val a fallback = Raw₀.Const.getD m a fallback := by
  simp [Raw.Const.getD, m.2]

theorem Const.get!_eq [BEq α] [Hashable α] [Inhabited β] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} :
    Raw.Const.get! m a = Raw₀.Const.get! ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.Const.get!, h.size_buckets_pos]

theorem Const.get!_val [BEq α] [Hashable α] [Inhabited β] {m : Raw₀ α (fun _ => β)} {a : α} :
    Raw.Const.get! m.val a = Raw₀.Const.get! m a := by
  simp [Raw.Const.get!, m.2]

theorem Const.fst_getThenInsertIfNew?_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {b : β} :
    (Raw.Const.getThenInsertIfNew? m a b).1 = (Raw₀.Const.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).1.1 := by
  simp [Raw.Const.getThenInsertIfNew?, h.size_buckets_pos]

theorem Const.fst_getThenInsertIfNew?_val [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)} {a : α} {b : β} :
    (Raw.Const.getThenInsertIfNew? m.val a b).1 = (Raw₀.Const.getThenInsertIfNew? m a b).1.1 := by
  simp [Raw.Const.getThenInsertIfNew?, m.2]

theorem Const.snd_getThenInsertIfNew?_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {b : β} :
    (Raw.Const.getThenInsertIfNew? m a b).2 = (Raw₀.Const.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).2 := by
  simp [Raw.Const.getThenInsertIfNew?, h.size_buckets_pos]

theorem Const.snd_getThenInsertIfNew?_val [BEq α] [Hashable α] {m : Raw₀ α (fun _ => β)} {a : α} {b : β} :
    (Raw.Const.getThenInsertIfNew? m.val a b).2 = (Raw₀.Const.getThenInsertIfNew? m a b).2 := by
  simp [Raw.Const.getThenInsertIfNew?, m.2]

end

end Raw

end Std.DHashMap.Internal
