/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic
import Hashmap.ForUpstream
import Hashmap.DHashMap.Internal.Model
import Hashmap.Leftovers
import Hashmap.AssocList.Lemmas

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

open List

namespace MyLean.DHashMap

@[simp]
theorem toListModel_mkArray_nil {c} : toListModel (mkArray c (AssocList.nil : AssocList α β)) = [] := by
  suffices ∀ d, (List.replicate d AssocList.nil).bind AssocList.toList = [] from this _
  intro d
  induction d <;> simp_all

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

-- TODO: clean up
theorem toList_perm_toListModel {m : Raw α β} : m.toList ~ toListModel m.buckets := by
  rw [Raw.toList, toListModel, List.bind_eq_foldl, Raw.foldl, Raw.foldlM, Array.foldlM_eq_foldlM_data, ← List.foldl_eq_foldlM, Id.run]
  have h₁ : ∀ {l : AssocList α β} {acc : List (Σ a, β a)}, l.foldlM (m := Id) (fun acc k v => ⟨k, v⟩ :: acc) acc =
      l.toList.reverse ++ acc := by
    intro l acc
    induction l generalizing acc
    · simp [AssocList.foldlM]
    · simp_all [AssocList.foldlM]
  simp only [h₁]
  suffices ∀ (l : List (AssocList α β)) (l₁ l₂), l₁ ~ l₂ →
      l.foldl (fun acc m => m.toList.reverse ++ acc) l₁ ~ l.foldl (fun acc m => acc ++ m.toList) l₂ by
    simpa using this m.buckets.data [] []
  intros l l₁ l₂ h
  induction l generalizing l₁ l₂
  · simpa
  · next l t ih =>
    simp only [foldl_cons]
    apply ih
    refine (List.reverse_perm _).append_right _ |>.trans List.perm_append_comm |>.trans ?_
    exact h.append_right l.toList

-- TODO: clean up
theorem values_eq_values_toList {β : Type v} {m : Raw α (fun _ => β)} : m.values = m.toList.values := by
  simp only [Raw.toList, List.values_eq_map, Raw.values, Raw.foldl, Raw.foldlM, Array.foldlM_eq_foldlM_data, ← List.foldl_eq_foldlM, Id.run]
  suffices ∀ (l : List (AssocList α (fun _ => β))) (l' : List ((_ : α) × β)),
      List.foldl (fun acc l => AssocList.foldlM (m := Id) (fun acc _ v => v :: acc) acc l) (l'.map (·.2)) l =
      List.map (fun x => x.snd) (List.foldl (fun acc l => AssocList.foldlM (m := Id) (fun acc k v => ⟨k, v⟩ :: acc) acc l) l' l) by
    simpa using this m.buckets.data []
  intros l l'
  induction l generalizing l'
  · simp
  · next h t ih =>
    simp only [foldl_cons]
    rw [← ih]
    congr
    induction h generalizing l'
    · simp [AssocList.foldlM]
    · next k v t ih' => simp [AssocList.foldlM, ← ih']

theorem values_perm_values_toListModel {β : Type v} {m : Raw α (fun _ => β)} : m.values ~ (toListModel m.buckets).values := by
  rw [values_eq_values_toList, values_eq_map, values_eq_map]
  exact (toList_perm_toListModel (m := m)).map _

theorem size_eq_length [BEq α] [Hashable α] {m : Raw α β} (h : m.WFImp) : m.size = (toListModel m.buckets).length :=
  h.size_eq

theorem isEmpty_eq_isEmpty [BEq α] [Hashable α] {m : Raw α β} (h : m.WFImp) : m.isEmpty = (toListModel m.buckets).isEmpty := by
  rw [isEmpty, Bool.eq_iff_iff, List.isEmpty_iff_length_eq_zero, size_eq_length h, Nat.beq_eq_true_eq]

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
    toListModel (reinsertAux hash data a b).1 ~ ⟨a, b⟩ :: toListModel data.1 := by
  rw [reinsertAux_eq]
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_update data.1 data.2 a (fun l => l.cons a b)
  exact h₂.trans (by simpa using h₁.symm)

theorem isHashSelf_foldl_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : AssocList α β) (target : { d : Array (AssocList α β) // 0 < d.size }) :
    IsHashSelf target.1 → IsHashSelf (l.foldl (reinsertAux hash) target).1 := by
  induction l generalizing target
  · simp [AssocList.foldl, AssocList.foldlM, Id.run]
  · next k v _ ih => exact fun h => ih _ (isHashSelf_reinsertAux _ _ _ h)

theorem toListModel_foldl_reinsertAux [BEq α] [Hashable α] [PartialEquivBEq α] (l : AssocList α β)
    (target : { d : Array (AssocList α β) // 0 < d.size }) :
    toListModel (l.foldl (reinsertAux hash) target).1 ~ l.toList ++ toListModel target.1 := by
  induction l generalizing target
  · simp
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
    toListModel (expand buckets).1 ~ toListModel buckets.1 := by
  rw [expand]
  refine (go _ _ _).trans ?_
  rw [drop_zero, toListModel_mkArray_nil, append_nil, toListModel]
  where
    go (i) (source : Array (AssocList α β)) (target : {d : Array (AssocList α β) // 0 < d.size}) :
        toListModel (expand.go i source target).1 ~ (source.data.drop i).bind AssocList.toList ++ toListModel target.1 := by
      induction i, source, target using expand.go.induct
      · next i source target hi _ es newSource newTarget ih =>
        simp only [newSource, newTarget, es] at *
        rw [expand.go_pos hi]
        refine ih.trans ?_
        rw [Array.size_eq_length_data] at hi
        rw [List.drop_eq_get_cons hi, List.cons_bind, Array.data_set, List.drop_set_of_lt _ _ (Nat.lt_succ_self i),
          Array.get_eq_getElem, Array.getElem_eq_data_get]
        refine ((toListModel_foldl_reinsertAux _ _).append_left _).trans ?_
        simp only [Nat.succ_eq_add_one, Array.data_length, append_assoc]
        exact List.perm_append_comm_assoc _ _ _
      · next i source target hi =>
        rw [expand.go_neg hi]
        rw [Array.size_eq_length_data, Nat.not_lt, ← List.drop_eq_nil_iff_le] at hi
        simp [hi]

theorem toListModel_expandIfNecessary [BEq α] [Hashable α] [PartialEquivBEq α] (m : Raw₀ α β) :
    toListModel (expandIfNecessary m).1.2 ~ toListModel m.1.2 := by
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
    m.containsₘ a = (toListModel m.1.buckets).containsKey a :=
  apply_bucket hm AssocList.contains_eq (fun _ => List.containsKey_of_perm) List.containsKey_append_of_not_contains_right

theorem contains_eq_containsKey [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} :
    m.contains a = (toListModel m.1.buckets).containsKey a := by
  rw [contains_eq_containsₘ, containsₘ_eq_containsKey hm]

theorem get?ₘ_eq_getValueCast? [BEq α] [Hashable α] [LawfulBEq α]
    {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} : m.get?ₘ a = (toListModel m.1.buckets).getValueCast? a :=
  apply_bucket hm AssocList.getCast?_eq List.getValueCast?_of_perm List.getValueCast?_append_of_containsKey_eq_false

theorem get?_eq_getValueCast? [BEq α] [Hashable α] [LawfulBEq α]
    {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} : m.get? a = (toListModel m.1.buckets).getValueCast? a := by
  rw [get?_eq_get?ₘ, get?ₘ_eq_getValueCast? hm]

theorem getₘ_eq_getValue [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {h : m.containsₘ a} :
    m.getₘ a h = (toListModel m.1.buckets).getValueCast a (containsₘ_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.getCast List.getValueCast AssocList.getCast_eq List.getValueCast_of_perm
    List.getValueCast_append_of_containsKey_eq_false

theorem get_eq_getValueCast [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {h : m.contains a} :
    m.get a h = (toListModel m.1.buckets).getValueCast a (contains_eq_containsKey hm ▸ h) := by
  rw [get_eq_getₘ, getₘ_eq_getValue hm]

theorem get!ₘ_eq_getValueCast! [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} [Inhabited (β a)] :
    m.get!ₘ a = (toListModel m.1.buckets).getValueCast! a := by
  rw [get!ₘ, get?ₘ_eq_getValueCast? hm, List.getValueCast!_eq_getValueCast?]

theorem get!_eq_getValueCast! [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} [Inhabited (β a)] :
    m.get! a = (toListModel m.1.buckets).getValueCast! a := by
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValueCast! hm]

theorem getDₘ_eq_getValueCastD [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {fallback : β a} :
    m.getDₘ a fallback = (toListModel m.1.buckets).getValueCastD a fallback := by
  rw [getDₘ, get?ₘ_eq_getValueCast? hm, List.getValueCastD_eq_getValueCast?]

theorem getD_eq_getValueCastD [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} {fallback : β a} :
    m.getD a fallback = (toListModel m.1.buckets).getValueCastD a fallback := by
  rw [getD_eq_getDₘ, getDₘ_eq_getValueCastD hm]

section

variable {β : Type v}

theorem Const.get?ₘ_eq_getValue? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get?ₘ m a = (toListModel m.1.buckets).getValue? a :=
  apply_bucket hm AssocList.get?_eq List.getValue?_of_perm getValue?_append_of_containsKey_eq_false

theorem Const.get?_eq_getValue? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get? m a = (toListModel m.1.buckets).getValue? a := by
  rw [Const.get?_eq_get?ₘ, Const.get?ₘ_eq_getValue? hm]

theorem Const.getₘ_eq_getValue [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {h} : Const.getₘ m a h = (toListModel m.1.buckets).getValue a (containsₘ_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.get List.getValue AssocList.get_eq List.getValue_of_perm List.getValue_append_of_containsKey_eq_false

theorem Const.get_eq_getValue [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {h} : Const.get m a h = (toListModel m.1.buckets).getValue a (contains_eq_containsKey hm ▸ h) := by
  rw [Const.get_eq_getₘ, Const.getₘ_eq_getValue hm]

theorem Const.get!ₘ_eq_getValue! [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] [Inhabited β] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get!ₘ m a = (toListModel m.1.buckets).getValue! a := by
  rw [get!ₘ, get?ₘ_eq_getValue? hm, List.getValue!_eq_getValue?]

theorem Const.get!_eq_getValue! [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] [Inhabited β] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} : Const.get! m a = (toListModel m.1.buckets).getValue! a := by
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValue! hm]

theorem Const.getDₘ_eq_getValueD [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {fallback : β} : Const.getDₘ m a fallback = (toListModel m.1.buckets).getValueD a fallback := by
  rw [getDₘ, get?ₘ_eq_getValue? hm, List.getValueD_eq_getValue?]

theorem Const.getD_eq_getValueD [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (hm : m.1.WFImp) {a : α} {fallback : β} : Const.getD m a fallback = (toListModel m.1.buckets).getValueD a fallback := by
  rw [getD_eq_getDₘ, getDₘ_eq_getValueD hm]

theorem mem_values_iff_mem_values_toListModel {m : Raw₀ α (fun _ => β)} {b : β} :
    b ∈ m.1.values ↔ b ∈ (toListModel m.1.buckets).values :=
  Raw.values_perm_values_toListModel.mem_iff

end

/-! # `replaceₘ` -/

theorem toListModel_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
   (h : m.1.WFImp) (a : α) (b : β a) : toListModel (m.replaceₘ a b).1.buckets ~ (toListModel m.1.2).replaceEntry a b :=
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
    (m : Raw₀ α β) (h : m.1.WFImp) (a : α) (b : β a) : toListModel (m.consₘ a b).1.buckets ~ ⟨a, b⟩ :: (toListModel m.1.2) :=
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
    (h : m.1.WFImp) {a : α} {b : β a} : toListModel (m.insertₘ a b).1.2 ~ (toListModel m.1.2).insertEntry a b := by
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
    (h : m.1.WFImp) {a : α} {b : β a} : toListModel (m.insert a b).1.2 ~ (toListModel m.1.2).insertEntry a b := by
  rw [insert_eq_insertₘ]
  exact toListModel_insertₘ h

theorem wfImp_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : (m.insert a b).1.WFImp := by
  rw [insert_eq_insertₘ]
  exact wfImp_insertₘ h

/-! # `containsThenInsert` -/

theorem toListModel_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : toListModel (m.containsThenInsert a b).1.1.2 ~ (toListModel m.1.2).insertEntry a b := by
  rw [containsThenInsert_eq_insertₘ]
  exact toListModel_insertₘ h

theorem wfImp_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : (m.containsThenInsert a b).1.1.WFImp := by
  rw [containsThenInsert_eq_insertₘ]
  exact wfImp_insertₘ h

/-! # `insertIfNewₘ` -/

theorem toListModel_insertIfNewₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : m.1.WFImp) {a : α} {b : β a} : toListModel (m.insertIfNewₘ a b).1.buckets ~ (toListModel m.1.buckets).insertEntryIfNew a b := by
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
    toListModel (m.insertIfNew a b).1.buckets ~ (toListModel m.1.buckets).insertEntryIfNew a b := by
  rw [insertIfNew_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem wfImp_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (h : m.1.WFImp) {a : α} {b : β a} :
    (m.insertIfNew a b).1.WFImp := by
  rw [insertIfNew_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `getThenInsertIfNew?` -/

theorem toListModel_getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {b : β a} (h : m.1.WFImp) :
    toListModel (m.getThenInsertIfNew? a b).1.1.buckets ~ (toListModel m.1.buckets).insertEntryIfNew a b := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem wfImp_getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α} {b : β a} (h : m.1.WFImp) :
    (m.getThenInsertIfNew? a b).1.1.WFImp := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `Const.getThenInsertIfNew?` -/

theorem Const.toListModel_getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} {a : α} {b : β} (h : m.1.WFImp) :
    toListModel (Const.getThenInsertIfNew? m a b).1.1.buckets ~ (toListModel m.1.buckets).insertEntryIfNew a b := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem Const.wfImp_getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} {a : α} {b : β} (h : m.1.WFImp) : (Const.getThenInsertIfNew? m a b).1.1.WFImp := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `removeₘ` -/

theorem toListModel_removeₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a : α)
    (h : m.1.WFImp) : toListModel (m.removeₘaux a).1.buckets ~ (toListModel m.1.buckets).removeKey a :=
  toListModel_updateBucket h AssocList.toList_remove List.removeKey_of_perm List.removeKey_append_of_containsKey_right_eq_false

theorem isHashSelf_removeₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a : α)
    (h : m.1.WFImp) : IsHashSelf (m.removeₘaux a).1.buckets := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  rw [AssocList.toList_remove] at hp
  exact Or.inl (containsKey_of_mem ((sublist_removeKey.subset hp)))

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
    toListModel m.1.buckets ~ (toListModel m.1.buckets).removeKey a := by
  rw [removeKey_of_containsKey_eq_false]
  rw [← containsₘ_eq_containsKey h, h']

theorem toListModel_removeₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : m.1.WFImp) : toListModel (m.removeₘ a).1.buckets ~ (toListModel m.1.buckets).removeKey a := by
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
    (h : m.1.WFImp) : toListModel (m.remove a).1.buckets ~ (toListModel m.1.buckets).removeKey a := by
  rw [remove_eq_removeₘ]
  exact toListModel_removeₘ h

theorem wfImp_remove [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : m.1.WFImp) : (m.remove a).1.WFImp := by
  rw [remove_eq_removeₘ]
  exact wfImp_removeₘ h

/-! # `filterMapₘ` -/

theorem toListModel_filterMapₘ {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} :
    toListModel (m.filterMapₘ f).1.buckets ~ (toListModel m.1.buckets).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩) :=
  toListModel_updateAllBuckets AssocList.toList_filterMap (by simp [List.filterMap_append])

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
    toListModel (m.filterMap f).1.buckets ~ (toListModel m.1.buckets).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩) := by
  rw [filterMap_eq_filterMapₘ]
  exact toListModel_filterMapₘ

theorem wfImp_filterMap [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} (h : m.1.WFImp) :
    (m.filterMap f).1.WFImp := by
  rw [filterMap_eq_filterMapₘ]
  exact wfImp_filterMapₘ h

/-! # `mapₘ` -/

theorem toListModel_mapₘ {m : Raw₀ α β} {f : (a : α) → β a → δ a} :
    toListModel (m.mapₘ f).1.buckets ~ (toListModel m.1.buckets).map fun p => ⟨p.1, f p.1 p.2⟩ :=
  toListModel_updateAllBuckets AssocList.toList_map (by simp)

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
    toListModel (m.map f).1.buckets ~ (toListModel m.1.buckets).map fun p => ⟨p.1, f p.1 p.2⟩ := by
  rw [map_eq_mapₘ]
  exact toListModel_mapₘ

theorem wfImp_map [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → δ a}
    (h : m.1.WFImp) : (m.map f).1.WFImp := by
  rw [map_eq_mapₘ]
  exact wfImp_mapₘ h

/-! # `filterₘ` -/

theorem toListModel_filterₘ {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    toListModel (m.filterₘ f).1.buckets ~ (toListModel m.1.buckets).filter fun p => f p.1 p.2 :=
  toListModel_updateAllBuckets AssocList.toList_filter (by simp)

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
    toListModel (m.filter f).1.buckets ~ (toListModel m.1.buckets).filter fun p => f p.1 p.2 := by
  rw [filter_eq_filterₘ]
  exact toListModel_filterₘ

theorem wfImp_filter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {f : (a : α) → β a → Bool}
    (h : m.1.WFImp) : (m.filter f).1.WFImp := by
  rw [filter_eq_filterₘ]
  exact wfImp_filterₘ h

end Raw₀

namespace Raw

namespace WFImp

alias empty := Raw₀.wfImp_empty
alias insert := Raw₀.wfImp_insert
alias containsThenInsert := Raw₀.wfImp_containsThenInsert
alias remove := Raw₀.wfImp_remove
alias filterMap := Raw₀.wfImp_filterMap
alias map := Raw₀.wfImp_map
alias insertIfNew := Raw₀.wfImp_insertIfNew
alias getThenInsertIfNew := Raw₀.wfImp_getThenInsertIfNew?
alias Const.getThenInsertIfNew := Raw₀.Const.wfImp_getThenInsertIfNew?
alias filter := Raw₀.wfImp_filter

end WFImp

theorem WF.out [BEq α] [Hashable α] [i₁ : EquivBEq α] [i₂ : LawfulHashable α] {m : Raw α β} (h : m.WF) : m.WFImp := by
  induction h generalizing i₁ i₂
  · next h => apply h
  · exact WFImp.empty
  · next h => exact WFImp.insert (by apply h)
  · next h => exact WFImp.containsThenInsert (by apply h)
  · next h => exact WFImp.remove (by apply h)
  · next h => exact WFImp.insertIfNew (by apply h)
  · next h => exact WFImp.getThenInsertIfNew (by apply h)
  · next h => exact WFImp.filter (by apply h)
  · next h => exact WFImp.Const.getThenInsertIfNew (by apply h)

-- TODO: rename the following theorems to make sure users don't apply them by accident

theorem empty_eq [BEq α] [Hashable α] {c : Nat} : (empty c : Raw α β) = (Raw₀.empty c).1 := rfl

theorem emptyc_eq [BEq α] [Hashable α] : (∅ : Raw α β) = Raw₀.empty.1 := rfl

theorem insert_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    m.insert a b = (Raw₀.insert ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [insert, h.size_buckets_pos]

theorem insertIfNew_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    m.insertIfNew a b = (Raw₀.insertIfNew ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [insertIfNew, h.size_buckets_pos]

theorem fst_containsThenInsert_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.containsThenInsert a b).1 = (Raw₀.containsThenInsert ⟨m, h.size_buckets_pos⟩ a b).1.1 := by
  simp [containsThenInsert, h.size_buckets_pos]

theorem snd_containsThenInsert_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.containsThenInsert a b).2 = (Raw₀.containsThenInsert ⟨m, h.size_buckets_pos⟩ a b).2 := by
  simp [containsThenInsert, h.size_buckets_pos]

theorem fst_getThenInsertIfNew?_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.getThenInsertIfNew? a b).1 = (Raw₀.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).1.1 := by
  simp [getThenInsertIfNew?, h.size_buckets_pos]

theorem snd_getThenInsertIfNew_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.getThenInsertIfNew? a b).2 = (Raw₀.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).2 := by
  simp [getThenInsertIfNew?, h.size_buckets_pos]

theorem get?_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} :
    m.get? a = Raw₀.get? ⟨m, h.size_buckets_pos⟩ a := by
  simp [get?, h.size_buckets_pos]

theorem contains_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} :
    m.contains a = Raw₀.contains ⟨m, h.size_buckets_pos⟩ a := by
  simp [contains, h.size_buckets_pos]

theorem get_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {a : α} {h : a ∈ m} :
    m.get a h = Raw₀.get ⟨m, by rw [mem_iff_contains, contains] at h; split at h <;> simp_all⟩ a (by rw [mem_iff_contains, contains] at h; split at h <;> simp_all) := rfl

theorem getD_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} {fallback : β a} :
    m.getD a fallback = Raw₀.getD ⟨m, h.size_buckets_pos⟩ a fallback := by
  simp [getD, h.size_buckets_pos]

theorem get!_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} [Inhabited (β a)] :
    m.get! a = Raw₀.get! ⟨m, h.size_buckets_pos⟩ a := by
  simp [get!, h.size_buckets_pos]

theorem remove_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} :
    m.remove a = Raw₀.remove ⟨m, h.size_buckets_pos⟩ a := by
  simp [remove, h.size_buckets_pos]

theorem filterMap_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → Option (δ a)} :
    m.filterMap f = Raw₀.filterMap f ⟨m, h.size_buckets_pos⟩ := by
  simp [filterMap, h.size_buckets_pos]

theorem map_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → δ a} :
    m.map f = Raw₀.map f ⟨m, h.size_buckets_pos⟩ := by
  simp [map, h.size_buckets_pos]

theorem filter_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → Bool} :
    m.filter f = Raw₀.filter f ⟨m, h.size_buckets_pos⟩ := by
  simp [filter, h.size_buckets_pos]

theorem WF.filterMap [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → Option (δ a)} :
    (m.filterMap f).WF := by
  simpa only [filterMap_eq h] using .wf (Raw₀.filterMap f ⟨m, h.size_buckets_pos⟩).2 (.filterMap h.out)

theorem WF.map [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → δ a} :
    (m.map f).WF := by
  simpa only [map_eq h] using .wf (Raw₀.map f ⟨m, h.size_buckets_pos⟩).2 (.map h.out)

section

variable {β : Type v}

theorem Const.get?_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} :
    Const.get? m a = Raw₀.Const.get? ⟨m, h.size_buckets_pos⟩ a := by
  simp [Const.get?, h.size_buckets_pos]

theorem Const.get_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {a : α} {h : a ∈ m} :
    Const.get m a h = Raw₀.Const.get ⟨m, by rw [mem_iff_contains, contains] at h; split at h <;> simp_all⟩ a (by rw [mem_iff_contains, contains] at h; split at h <;> simp_all) :=
  rfl

theorem Const.getD_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {fallback : β} :
    Const.getD m a fallback = Raw₀.Const.getD ⟨m, h.size_buckets_pos⟩ a fallback := by
  simp [Const.getD, h.size_buckets_pos]

theorem Const.get!_eq [BEq α] [Hashable α] [Inhabited β] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} :
    Const.get! m a = Raw₀.Const.get! ⟨m, h.size_buckets_pos⟩ a := by
  simp [Const.get!, h.size_buckets_pos]

theorem Const.fst_getThenInsertIfNew?_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {b : β} :
    (Const.getThenInsertIfNew? m a b).1 = (Raw₀.Const.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).1.1 := by
  simp [Const.getThenInsertIfNew?, h.size_buckets_pos]

theorem Const.snd_getThenInsertIfNew?_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} {b : β} :
    (Const.getThenInsertIfNew? m a b).2 = (Raw₀.Const.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).2 := by
  simp [Const.getThenInsertIfNew?, h.size_buckets_pos]

end

end Raw

theorem empty_eq [BEq α] [Hashable α] {c : Nat} : (empty c : DHashMap α β).1 = (Raw₀.empty c).1 := rfl

theorem emptyc_eq [BEq α] [Hashable α] : (∅ : DHashMap α β).1 = Raw₀.empty.1 := rfl

end MyLean.DHashMap
