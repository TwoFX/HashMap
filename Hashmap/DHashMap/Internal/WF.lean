/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic
import Hashmap.DHashMap.Internal.Model
import Hashmap.DHashMap.Internal.AssocList.Lemmas

open MyLean.DHashMap.Internal.List

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

open List

namespace MyLean.DHashMap.Internal

@[simp]
theorem toListModel_mkArray_nil {c} : toListModel (mkArray c (AssocList.nil : AssocList α β)) = [] := by
  suffices ∀ d, (List.replicate d AssocList.nil).bind AssocList.toList = [] from this _
  intro d
  induction d <;> simp_all [List.replicate]

@[simp]
theorem computeSize_eq {buckets : Array (AssocList α β)} : computeSize buckets = (toListModel buckets).length := by
  rw [computeSize, toListModel, List.bind_eq_foldl, Array.foldl_eq_foldl_data]
  suffices ∀ (l : List (AssocList α β)) (l' : List (Σ a, β a)),
      l.foldl (fun d b => d + b.toList.length) l'.length = (l.foldl (fun acc a => acc ++ a.toList) l').length
    by simpa using this buckets.data []
  intro l l'
  induction l generalizing l'
  · simp
  · next l₂ t ih => rw [foldl_cons, ← List.length_append, ih, foldl_cons]

namespace Raw

theorem size_eq_length [BEq α] [Hashable α] {m : Raw α β} (h : m.WFImp) : m.size = (toListModel m.buckets).length :=
  h.size_eq

theorem isEmpty_eq_isEmpty [BEq α] [Hashable α] {m : Raw α β} (h : m.WFImp) : m.isEmpty = (toListModel m.buckets).isEmpty := by
  rw [Raw.isEmpty, Bool.eq_iff_iff, List.isEmpty_iff_length_eq_zero, size_eq_length h, Nat.beq_eq_true_eq]

end Raw

namespace Raw₀

/-! # Raw₀.empty -/

@[simp]
theorem toListModel_buckets_empty {c} : toListModel (empty c : Raw₀ α β).1.buckets = [] :=
  toListModel_mkArray_nil

theorem wfImp_empty [BEq α] [Hashable α] {c} : (empty c : Raw₀ α β).1.WFImp where
  buckets_hash_self := by simp [Raw.empty, Raw₀.empty]
  buckets_size := Raw.WF.empty₀.size_buckets_pos
  size_eq := by simp [Raw.empty, Raw₀.empty]
  distinct := by simp

theorem isHashSelf_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) (h : IsHashSelf data.1) :
    IsHashSelf (reinsertAux hash data a b).1 := by
  rw [reinsertAux_eq]
  refine h.updateBucket (fun l p hp => ?_)
  simp only [AssocList.toList_cons, mem_cons] at hp
  rcases hp with (rfl|hp)
  · exact Or.inr rfl
  · exact Or.inl (containsKey_of_mem hp)

/-! # expandIfNecessary -/

theorem toListModel_reinsertAux [BEq α] [Hashable α] [PartialEquivBEq α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) :
    Perm (toListModel (reinsertAux hash data a b).1) (⟨a, b⟩ :: toListModel data.1) := by
  rw [reinsertAux_eq]
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_update data.1 data.2 a (fun l => l.cons a b)
  refine h₂.trans ?_
  simpa using Perm.cons _ (Perm.symm h₁)

theorem isHashSelf_foldl_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : AssocList α β) (target : { d : Array (AssocList α β) // 0 < d.size }) :
    IsHashSelf target.1 → IsHashSelf (l.foldl (reinsertAux hash) target).1 := by
  induction l generalizing target
  · simp [AssocList.foldl, AssocList.foldlM, Id.run]
  · next k v _ ih => exact fun h => ih _ (isHashSelf_reinsertAux _ _ _ h)

theorem toListModel_foldl_reinsertAux [BEq α] [Hashable α] [PartialEquivBEq α] (l : AssocList α β)
    (target : { d : Array (AssocList α β) // 0 < d.size }) :
    Perm (toListModel (l.foldl (reinsertAux hash) target).1) (l.toList ++ toListModel target.1) := by
  induction l generalizing target
  · simpa using Perm.refl _
  · next k v t ih =>
    skip
    simp at ih
    simp
    refine (ih _).trans ?_
    refine ((toListModel_reinsertAux _ _ _).append_left _).trans perm_middle

theorem expand.go_pos [Hashable α] {i : Nat} {source : Array (AssocList α β)} {target : { d : Array (AssocList α β) // 0 < d.size }}
    (h : i < source.size) : expand.go i source target =
      go (i + 1) (source.set ⟨i, h⟩ .nil) ((source.get ⟨i, h⟩).foldl (reinsertAux hash) target) := by
  rw [expand.go]
  simp only [h, dite_true]

theorem expand.go_neg [Hashable α] {i : Nat} {source : Array (AssocList α β)} {target : { d : Array (AssocList α β) // 0 < d.size}}
    (h : ¬i < source.size) : expand.go i source target = target := by
  rw [expand.go]
  simp only [h, dite_false]

theorem isHashSelf_expand [BEq α] [Hashable α] [LawfulHashable α] [EquivBEq α] {buckets : {d : Array (AssocList α β) // 0 < d.size}} :
    IsHashSelf (expand buckets).1 := by
  rw [expand]
  apply go
  simp only [IsHashSelf.mkArray]
  where
    go (i) (source : Array (AssocList α β)) (target : {d : Array (AssocList α β) // 0 < d.size}) :
        IsHashSelf target.1 → IsHashSelf (expand.go i source target).1 := by
      induction i, source, target using expand.go.induct
      · next i source target hi _ es newSource newTarget ih =>
        simp only [newSource, newTarget, es] at *
        rw [expand.go_pos hi]
        refine ih ∘ ?_
        exact isHashSelf_foldl_reinsertAux _ _
      · next i source target hi =>
        rw [expand.go_neg hi]
        exact id

theorem toListModel_expand [BEq α] [Hashable α] [PartialEquivBEq α] {buckets : {d : Array (AssocList α β) // 0 < d.size}} :
    Perm (toListModel (expand buckets).1) (toListModel buckets.1) := by
  rw [expand]
  refine (go _ _ _).trans ?_
  rw [drop_zero, toListModel_mkArray_nil, append_nil, toListModel]
  exact Perm.refl _
  where
    go (i) (source : Array (AssocList α β)) (target : {d : Array (AssocList α β) // 0 < d.size}) :
        Perm (toListModel (expand.go i source target).1) ((source.data.drop i).bind AssocList.toList ++ toListModel target.1) := by
      induction i, source, target using expand.go.induct
      · next i source target hi _ es newSource newTarget ih =>
        simp only [newSource, newTarget, es] at *
        rw [expand.go_pos hi]
        refine ih.trans ?_
        rw [Array.size_eq_length_data] at hi
        rw [List.drop_eq_getElem_cons hi, List.bind_cons, Array.data_set, List.drop_set_of_lt _ _ (Nat.lt_succ_self i),
          Array.get_eq_getElem, Array.getElem_eq_data_getElem]
        refine ((toListModel_foldl_reinsertAux _ _).append_left _).trans ?_
        simp only [Nat.succ_eq_add_one, Array.data_length, append_assoc]
        exact perm_append_comm_assoc _ _ _
      · next i source target hi =>
        rw [expand.go_neg hi]
        rw [Array.size_eq_length_data, Nat.not_lt, ← List.drop_eq_nil_iff_le] at hi
        simpa [hi] using Perm.refl _

theorem toListModel_expandIfNecessary [BEq α] [Hashable α] [PartialEquivBEq α] (m : Raw₀ α β) :
    Perm (toListModel (expandIfNecessary m).1.2) (toListModel m.1.2) := by
  rw [expandIfNecessary]
  dsimp
  split
  · exact Perm.refl _
  · dsimp
    exact toListModel_expand

theorem wfImp_expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) : (expandIfNecessary m).1.WFImp := by
  rw [Raw₀.expandIfNecessary]
  dsimp
  split
  · exact h
  · let ⟨⟨size, buckets⟩, hm⟩ := m
    have := toListModel_expand (buckets := ⟨buckets, hm⟩)
    dsimp at this
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using isHashSelf_expand
    · simpa using (expand _).2
    · refine h.size_eq.trans ?_
      simpa using this.symm.length_eq
    · simpa using h.distinct.perm this

/-! # Access operations -/

theorem containsₘ_eq_containsKey [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} :
    m.containsₘ a = containsKey a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.contains_eq (fun _ => List.containsKey_of_perm) List.containsKey_append_of_not_contains_right

theorem contains_eq_containsKey [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} :
    m.contains a = containsKey a (toListModel m.1.buckets) := by
  rw [contains_eq_containsₘ, containsₘ_eq_containsKey hm]

theorem get?ₘ_eq_getValueCast? [BEq α] [Hashable α] [LawfulBEq α]
    {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} : m.get?ₘ a = getValueCast? a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.getCast?_eq List.getValueCast?_of_perm List.getValueCast?_append_of_containsKey_eq_false

theorem get?_eq_getValueCast? [BEq α] [Hashable α] [LawfulBEq α]
    {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} : m.get? a = getValueCast? a (toListModel m.1.buckets) := by
  rw [get?_eq_get?ₘ, get?ₘ_eq_getValueCast? hm]

theorem getₘ_eq_getValue [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {h : m.containsₘ a} :
    m.getₘ a h = getValueCast a (toListModel m.1.buckets) (containsₘ_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.getCast List.getValueCast AssocList.getCast_eq List.getValueCast_of_perm
    List.getValueCast_append_of_containsKey_eq_false

theorem get_eq_getValueCast [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {h : m.contains a} :
    m.get a h = getValueCast a (toListModel m.1.buckets) (contains_eq_containsKey hm ▸ h) := by
  rw [get_eq_getₘ, getₘ_eq_getValue hm]

theorem get!ₘ_eq_getValueCast! [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} [Inhabited (β a)] :
    m.get!ₘ a = getValueCast! a (toListModel m.1.buckets) := by
  rw [get!ₘ, get?ₘ_eq_getValueCast? hm, List.getValueCast!_eq_getValueCast?]

theorem get!_eq_getValueCast! [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} [Inhabited (β a)] :
    m.get! a = getValueCast! a (toListModel m.1.buckets) := by
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValueCast! hm]

theorem getDₘ_eq_getValueCastD [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {fallback : β a} :
    m.getDₘ a fallback = getValueCastD a (toListModel m.1.buckets) fallback := by
  rw [getDₘ, get?ₘ_eq_getValueCast? hm, List.getValueCastD_eq_getValueCast?]

theorem getD_eq_getValueCastD [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {fallback : β a} :
    m.getD a fallback = getValueCastD a (toListModel m.1.buckets) fallback := by
  rw [getD_eq_getDₘ, getDₘ_eq_getValueCastD hm]

section

variable {β : Type v}

theorem Const.get?ₘ_eq_getValue? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get?ₘ m a = getValue? a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.get?_eq List.getValue?_of_perm getValue?_append_of_containsKey_eq_false

theorem Const.get?_eq_getValue? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get? m a = getValue? a (toListModel m.1.buckets) := by
  rw [Const.get?_eq_get?ₘ, Const.get?ₘ_eq_getValue? hm]

theorem Const.getₘ_eq_getValue [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {h} : Const.getₘ m a h = getValue a (toListModel m.1.buckets) (containsₘ_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.get List.getValue AssocList.get_eq List.getValue_of_perm List.getValue_append_of_containsKey_eq_false

theorem Const.get_eq_getValue [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {h} : Const.get m a h = getValue a (toListModel m.1.buckets) (contains_eq_containsKey hm ▸ h) := by
  rw [Const.get_eq_getₘ, Const.getₘ_eq_getValue hm]

theorem Const.get!ₘ_eq_getValue! [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] [Inhabited β] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get!ₘ m a = getValue! a (toListModel m.1.buckets) := by
  rw [get!ₘ, get?ₘ_eq_getValue? hm, List.getValue!_eq_getValue?]

theorem Const.get!_eq_getValue! [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] [Inhabited β] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get! m a = getValue! a (toListModel m.1.buckets) := by
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValue! hm]

theorem Const.getDₘ_eq_getValueD [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {fallback : β} : Const.getDₘ m a fallback = getValueD a (toListModel m.1.buckets) fallback := by
  rw [getDₘ, get?ₘ_eq_getValue? hm, List.getValueD_eq_getValue?]

theorem Const.getD_eq_getValueD [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {fallback : β} : Const.getD m a fallback = getValueD a (toListModel m.1.buckets) fallback := by
  rw [getD_eq_getDₘ, getDₘ_eq_getValueD hm]

-- theorem mem_values_iff_mem_values_toListModel {m : Raw₀ α (fun _ => β)} {b : β} :
--     b ∈ m.1.values ↔ b ∈ values (toListModel m.1.buckets) :=
--   Raw.values_perm_values_toListModel.mem_iff

end

/-! # `replaceₘ` -/

theorem toListModel_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
   (h : m.1.WFImp) (a : α) (b : β a) : Perm (toListModel (m.replaceₘ a b).1.buckets) (replaceEntry a b (toListModel m.1.2)) :=
  toListModel_updateBucket h AssocList.toList_replace List.replaceEntry_of_perm List.replaceEntry_append_of_containsKey_right_eq_false

theorem isHashSelf_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : IsHashSelf (m.replaceₘ a b).1.buckets := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  exact Or.inl (by simpa using containsKey_of_mem hp)

theorem wfImp_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : (m.replaceₘ a b).1.WFImp where
  buckets_hash_self := isHashSelf_replaceₘ m h a b
  buckets_size := by simpa [replaceₘ] using h.buckets_size
  size_eq := h.size_eq.trans (Eq.trans length_replaceEntry.symm (toListModel_replaceₘ _ h _ _).length_eq.symm)
  distinct := h.distinct.replaceEntry.perm (toListModel_replaceₘ _ h _ _)

/-! # `insertₘ` -/

theorem toListModel_consₘ [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.WFImp) (a : α) (b : β a) : Perm (toListModel (m.consₘ a b).1.buckets) (⟨a, b⟩ :: (toListModel m.1.2)) :=
  toListModel_updateBucket h rfl (fun _ => Perm.cons _) (fun _ => cons_append _ _ _)

theorem isHashSelf_consₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : IsHashSelf (m.consₘ a b).1.buckets := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  simp only [AssocList.toList_cons, mem_cons] at hp
  rcases hp with (rfl|hp)
  · exact Or.inr rfl
  · exact Or.inl (containsKey_of_mem hp)

theorem wfImp_consₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) (hc : m.containsₘ a = false) : (m.consₘ a b).1.WFImp where
  buckets_hash_self := isHashSelf_consₘ m h a b
  buckets_size := by simpa [consₘ] using h.buckets_size
  size_eq := by
    refine Eq.trans ?_ (toListModel_consₘ _ h _ _).length_eq.symm
    simpa [consₘ] using h.size_eq
  distinct := by
    refine (h.distinct.cons ?_).perm (toListModel_consₘ _ h _ _)
    rwa [← containsₘ_eq_containsKey h]

theorem toListModel_insertₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : Perm (toListModel (m.insertₘ a b).1.2) (insertEntry a b (toListModel m.1.2)) := by
  rw [insertₘ]
  split
  · next h' =>
    rw [containsₘ_eq_containsKey h] at h'
    rw [insertEntry_of_containsKey h']
    exact toListModel_replaceₘ _ h _ _
  · next h' =>
    rw [containsₘ_eq_containsKey h, Bool.not_eq_true] at h'
    rw [insertEntry_of_containsKey_eq_false h']
    refine (Raw₀.toListModel_expandIfNecessary _).trans ?_
    exact toListModel_consₘ m h a b

theorem wfImp_insertₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : (m.insertₘ a b).1.WFImp := by
  rw [insertₘ]
  split
  · apply wfImp_replaceₘ _ h
  · apply wfImp_expandIfNecessary
    apply wfImp_consₘ _ h _ _ (by simp_all)

/-! # `insert` -/

theorem toListModel_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : Perm (toListModel (m.insert a b).1.2) (insertEntry a b (toListModel m.1.2)) := by
  rw [insert_eq_insertₘ]
  exact toListModel_insertₘ h

theorem wfImp_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : (m.insert a b).1.WFImp := by
  rw [insert_eq_insertₘ]
  exact wfImp_insertₘ h

/-! # `containsThenInsert` -/

theorem toListModel_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : Perm (toListModel (m.containsThenInsert a b).1.1.2) (insertEntry a b (toListModel m.1.2)) := by
  rw [containsThenInsert_eq_insertₘ]
  exact toListModel_insertₘ h

theorem wfImp_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : (m.containsThenInsert a b).1.1.WFImp := by
  rw [containsThenInsert_eq_insertₘ]
  exact wfImp_insertₘ h

/-! # `insertIfNewₘ` -/

theorem toListModel_insertIfNewₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : Perm (toListModel (m.insertIfNewₘ a b).1.buckets) (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [insertIfNewₘ, insertEntryIfNew, containsₘ_eq_containsKey h, cond_eq_if]
  split
  · next h' => exact Perm.refl _
  · next h' => exact (toListModel_expandIfNecessary _).trans (toListModel_consₘ m h a b)

theorem wfImp_insertIfNewₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : (m.insertIfNewₘ a b).1.WFImp := by
  rw [insertIfNewₘ]
  split
  · exact h
  · apply wfImp_expandIfNecessary
    apply wfImp_consₘ _ h _ _ (by simp_all)

/-! # `insertIfNew` -/

theorem toListModel_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} :
    Perm (toListModel (m.insertIfNew a b).1.buckets) (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [insertIfNew_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem wfImp_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (h : m.1.WFImp) {a : α} {b : β a} :
    (m.insertIfNew a b).1.WFImp := by
  rw [insertIfNew_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `getThenInsertIfNew?` -/

theorem toListModel_getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {b : β a} (h : m.1.WFImp) :
    Perm (toListModel (m.getThenInsertIfNew? a b).1.1.buckets) (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem wfImp_getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {b : β a} (h : m.1.WFImp) :
    (m.getThenInsertIfNew? a b).1.1.WFImp := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `Const.getThenInsertIfNew?` -/

theorem Const.toListModel_getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} {a : α} {b : β} (h : m.1.WFImp) :
    Perm (toListModel (Const.getThenInsertIfNew? m a b).1.1.buckets) (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem Const.wfImp_getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} {a : α} {b : β} (h : m.1.WFImp) : (Const.getThenInsertIfNew? m a b).1.1.WFImp := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `removeₘ` -/

theorem toListModel_removeₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a : α)
    (h : m.1.WFImp) : Perm (toListModel (m.removeₘaux a).1.buckets) (removeKey a (toListModel m.1.buckets)) :=
  toListModel_updateBucket h AssocList.toList_remove List.removeKey_of_perm List.removeKey_append_of_containsKey_right_eq_false

theorem isHashSelf_removeₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a : α)
    (h : m.1.WFImp) : IsHashSelf (m.removeₘaux a).1.buckets := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  rw [AssocList.toList_remove] at hp
  exact Or.inl (containsKey_of_mem ((sublist_removeKey.mem hp)))

theorem wfImp_removeₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a : α)
    (h : m.1.WFImp) (h' : m.containsₘ a = true) : (m.removeₘaux a).1.WFImp where
  buckets_hash_self := isHashSelf_removeₘaux m a h
  buckets_size := by simpa [removeₘaux] using h.buckets_size
  size_eq := by
    rw [(toListModel_removeₘaux m a h).length_eq, removeₘaux, length_removeKey,
      ← containsₘ_eq_containsKey h, h', cond_true, h.size_eq]
  distinct := h.distinct.removeKey.perm (toListModel_removeₘaux m a h)

theorem toListModel_perm_removeKey_of_containsₘ_eq_false [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (a : α) (h : m.1.WFImp) (h' : m.containsₘ a = false) :
    Perm (toListModel m.1.buckets) (removeKey a (toListModel m.1.buckets)) := by
  rw [removeKey_of_containsKey_eq_false]
  · exact Perm.refl _
  · rw [← containsₘ_eq_containsKey h, h']

theorem toListModel_removeₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : m.1.WFImp) : Perm (toListModel (m.removeₘ a).1.buckets) (removeKey a (toListModel m.1.buckets)) := by
  rw [removeₘ]
  split
  · exact toListModel_removeₘaux m a h
  · next h' =>
    exact toListModel_perm_removeKey_of_containsₘ_eq_false _ _ h (eq_false_of_ne_true h')

theorem wfImp_removeₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : m.1.WFImp) : (m.removeₘ a).1.WFImp := by
  rw [removeₘ]
  split
  · next h' => exact wfImp_removeₘaux m a h h'
  · exact h

/-! # `remove` -/

theorem toListModel_remove [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : m.1.WFImp) : Perm (toListModel (m.remove a).1.buckets) (removeKey a (toListModel m.1.buckets)) := by
  rw [remove_eq_removeₘ]
  exact toListModel_removeₘ h

theorem wfImp_remove [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : m.1.WFImp) : (m.remove a).1.WFImp := by
  rw [remove_eq_removeₘ]
  exact wfImp_removeₘ h

/-! # `filterMapₘ` -/

theorem toListModel_filterMapₘ {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} :
    Perm (toListModel (m.filterMapₘ f).1.buckets) ((toListModel m.1.buckets).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) :=
  toListModel_updateAllBuckets AssocList.toList_filterMap (by simp [List.filterMap_append]; exact Perm.refl _)

theorem isHashSelf_filterMapₘ [BEq α] [Hashable α] [ReflBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} (h : m.1.WFImp) :
    IsHashSelf (m.filterMapₘ f).1.buckets := by
  refine h.buckets_hash_self.updateAllBuckets (fun l p hp => ?_)
  have hp := AssocList.toList_filterMap.mem_iff.1 hp
  simp only [mem_filterMap, Option.map_eq_some'] at hp
  obtain ⟨p, ⟨hkv, ⟨d, ⟨-, rfl⟩⟩⟩⟩ := hp
  exact containsKey_of_mem hkv

theorem wfImp_filterMapₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} (h : m.1.WFImp) :
    (m.filterMapₘ f).1.WFImp where
  buckets_hash_self := isHashSelf_filterMapₘ h
  buckets_size := by simpa [filterMapₘ] using h.buckets_size
  size_eq := by simp [filterMapₘ]
  distinct := h.distinct.filterMap.perm toListModel_filterMapₘ

/-! # `filterMap` -/

theorem toListModel_filterMap {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} :
    Perm (toListModel (m.filterMap f).1.buckets) ((toListModel m.1.buckets).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  rw [filterMap_eq_filterMapₘ]
  exact toListModel_filterMapₘ

theorem wfImp_filterMap [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} (h : m.1.WFImp) :
    (m.filterMap f).1.WFImp := by
  rw [filterMap_eq_filterMapₘ]
  exact wfImp_filterMapₘ h

/-! # `mapₘ` -/

theorem toListModel_mapₘ {m : Raw₀ α β} {f : (a : α) → β a → δ a} :
    Perm (toListModel (m.mapₘ f).1.buckets) ((toListModel m.1.buckets).map fun p => ⟨p.1, f p.1 p.2⟩) :=
  toListModel_updateAllBuckets AssocList.toList_map (by simp; exact Perm.refl _)

theorem isHashSelf_mapₘ [BEq α] [Hashable α] [ReflBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → δ a}
    (h : m.1.WFImp) : IsHashSelf (m.mapₘ f).1.buckets := by
  refine h.buckets_hash_self.updateAllBuckets (fun l p hp => ?_)
  have hp := AssocList.toList_map.mem_iff.1 hp
  obtain ⟨p, hp₁, rfl⟩ := mem_map.1 hp
  exact containsKey_of_mem hp₁

theorem wfImp_mapₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → δ a}
    (h : m.1.WFImp) : (m.mapₘ f).1.WFImp where
  buckets_hash_self := isHashSelf_mapₘ h
  buckets_size := by simpa [mapₘ] using h.buckets_size
  size_eq := by rw [toListModel_mapₘ.length_eq, List.length_map, ← h.size_eq, mapₘ]
  distinct := h.distinct.map.perm toListModel_mapₘ

/-! # `map` -/

theorem toListModel_map {m : Raw₀ α β} {f : (a : α) → β a → δ a} :
    Perm (toListModel (m.map f).1.buckets) ((toListModel m.1.buckets).map fun p => ⟨p.1, f p.1 p.2⟩) := by
  rw [map_eq_mapₘ]
  exact toListModel_mapₘ

theorem wfImp_map [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → δ a}
    (h : m.1.WFImp) : (m.map f).1.WFImp := by
  rw [map_eq_mapₘ]
  exact wfImp_mapₘ h

/-! # `filterₘ` -/

theorem toListModel_filterₘ {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    Perm (toListModel (m.filterₘ f).1.buckets) ((toListModel m.1.buckets).filter fun p => f p.1 p.2) :=
  toListModel_updateAllBuckets AssocList.toList_filter (by simp; exact Perm.refl _)

theorem isHashSelf_filterₘ [BEq α] [Hashable α] [ReflBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → Bool} (h : m.1.WFImp) : IsHashSelf (m.filterₘ f).1.buckets := by
  refine h.buckets_hash_self.updateAllBuckets (fun l p hp => ?_)
  have hp := AssocList.toList_filter.mem_iff.1 hp
  obtain ⟨hp, -⟩ := mem_filter.1 hp
  exact containsKey_of_mem hp

theorem wfImp_filterₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Bool}
    (h : m.1.WFImp) : (m.filterₘ f).1.WFImp where
  buckets_hash_self := isHashSelf_filterₘ h
  buckets_size := by simpa [filterₘ] using h.buckets_size
  size_eq := by simp [filterₘ]
  distinct := h.distinct.filter.perm toListModel_filterₘ

/-! # `filter` -/

theorem toListModel_filter {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    Perm (toListModel (m.filter f).1.buckets) ((toListModel m.1.buckets).filter fun p => f p.1 p.2) := by
  rw [filter_eq_filterₘ]
  exact toListModel_filterₘ

theorem wfImp_filter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Bool}
    (h : m.1.WFImp) : (m.filter f).1.WFImp := by
  rw [filter_eq_filterₘ]
  exact wfImp_filterₘ h

end Raw₀

namespace Raw

namespace WFImp

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]

theorem empty {c : Nat} : (Raw₀.empty c : Raw₀ α β).val.WFImp := Raw₀.wfImp_empty
theorem insert [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (h : m.val.WFImp) {a : α} {b : β a} : (m.insert a b).val.WFImp := Raw₀.wfImp_insert h
theorem containsThenInsert [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (h : m.val.WFImp) {a : α} {b : β a} : (m.containsThenInsert a b).fst.val.WFImp := Raw₀.wfImp_containsThenInsert h
theorem remove [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α} (h : m.val.WFImp) : (m.remove a).val.WFImp := Raw₀.wfImp_remove h
theorem filterMap {δ : α → Type w} [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} (h : m.val.WFImp) : (Raw₀.filterMap f m).val.WFImp := Raw₀.wfImp_filterMap h
theorem map {δ : α → Type w} [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → δ a} (h : m.val.WFImp) : (Raw₀.map f m).val.WFImp := Raw₀.wfImp_map h
theorem insertIfNew [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (h : m.val.WFImp) {a : α} {b : β a} : (m.insertIfNew a b).val.WFImp := Raw₀.wfImp_insertIfNew h
theorem getThenInsertIfNew? [LawfulBEq α] {m : Raw₀ α β} {a : α} {b : β a} (h : m.val.WFImp) : (m.getThenInsertIfNew? a b).fst.val.WFImp := Raw₀.wfImp_getThenInsertIfNew? h
theorem Const.getThenInsertIfNew? {β : Type v} [EquivBEq α] [LawfulHashable α] {m : Raw₀ α fun _ => β} {a : α} {b : β} (h : m.val.WFImp) : (Raw₀.Const.getThenInsertIfNew? m a b).fst.val.WFImp := Raw₀.Const.wfImp_getThenInsertIfNew? h
theorem filter [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Bool} (h : m.val.WFImp) : (Raw₀.filter f m).val.WFImp := Raw₀.wfImp_filter h

end WFImp

theorem _root_.MyLean.DHashMap.Raw.WF.out [BEq α] [Hashable α] [i₁ : EquivBEq α] [i₂ : LawfulHashable α] {m : Raw α β} (h : m.WF) : m.WFImp := by
  induction h generalizing i₁ i₂
  · next h => apply h
  · exact WFImp.empty
  · next h => exact WFImp.insert (by apply h)
  · next h => exact WFImp.containsThenInsert (by apply h)
  · next h => exact WFImp.remove (by apply h)
  · next h => exact WFImp.insertIfNew (by apply h)
  · next h => exact WFImp.getThenInsertIfNew? (by apply h)
  · next h => exact WFImp.filter (by apply h)
  · next h => exact WFImp.Const.getThenInsertIfNew? (by apply h)

-- TODO: rename the following theorems to make sure users don't apply them by accident

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

end MyLean.DHashMap.Internal
