/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic
import Hashmap.DHashMap.ForUpstream
import Hashmap.DHashMap.Model

set_option autoImplicit false

universe u v

variable {α : Type v} {β : α → Type v}

open List

namespace MyLean.DHashMap

@[simp]
theorem toListModel_mkArray_nil {c} : toListModel (mkArray c (AssocList.nil : AssocList α β)) = [] := by
  suffices ∀ d, (List.replicate d AssocList.nil).bind AssocList.toList = [] from this _
  intro d
  induction d <;> simp_all

/-! # IsHashSelf -/

namespace IsHashSelf

@[simp]
theorem mkArray [BEq α] [Hashable α] {c : Nat} : IsHashSelf (mkArray c (AssocList.nil : AssocList α β)) :=
  ⟨by simp⟩

theorem uset [BEq α] [Hashable α] {m : Array (AssocList α β)} {i : USize} {h : i.toNat < m.size} {d : AssocList α β}
    (hd : m[i].toList.HashesTo i.toNat m.size → d.toList.HashesTo i.toNat m.size) (hm : IsHashSelf m) : IsHashSelf (m.uset i d h) := by
  refine ⟨fun j hj => ?_⟩
  simp only [Array.uset, Array.getElem_set, Array.size_set]
  split
  · next hij => exact hij ▸ (hd (hm.hashes_to _ _))
  · exact hm.hashes_to j (by simpa using hj)

theorem updateBucket [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Array (AssocList α β)} {h : 0 < m.size} {a : α} {f : AssocList α β → AssocList α β}
    (hf : ∀ l p, p ∈ (f l).toList → l.toList.containsKey p.1 ∨ hash p.1 = hash a) (hm : IsHashSelf m) : IsHashSelf (updateBucket m h a f) := by
  rw [DHashMap.updateBucket]
  refine IsHashSelf.uset (fun h' => ⟨fun _ p hp => ?_⟩) hm
  rcases hf _ _ hp with (hf|hf)
  · rw [containsKey_eq_true_iff_exists_mem] at hf
    rcases hf with ⟨q, hq₁, hq₂⟩
    rw [← h'.hash_self h _ hq₁, hash_eq hq₂]
  · rw [hf]

end IsHashSelf

namespace Raw₀

/-! # Raw₀.empty -/

@[simp]
theorem size_empty {c} : (empty c : Raw₀ α β).1.size = 0 := rfl

@[simp]
theorem toListModel_buckets_empty {c} : toListModel (empty c : Raw₀ α β).1.buckets = [] :=
  toListModel_mkArray_nil

theorem wfImp_empty [BEq α] [Hashable α] {c} : (empty c : Raw₀ α β).1.WFImp where
  buckets_hash_self := by simp [Raw.empty, Raw₀.empty]
  buckets_size := Raw.WF.empty.size_buckets_pos
  size_eq := by simp
  distinct := by simp

theorem isHashSelf_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) (h : IsHashSelf data.1) :
    IsHashSelf (reinsertAux data a b).1 := by
  rw [reinsertAux_eq]
  refine h.updateBucket (fun l p hp => ?_)
  simp only [AssocList.toList_cons, mem_cons] at hp
  rcases hp with (rfl|hp)
  · exact Or.inr rfl
  · exact Or.inl (containsKey_of_mem hp)

/-! # expandIfNecessary -/

theorem toListModel_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) :
    toListModel (reinsertAux data a b).1 ~ ⟨a, b⟩ :: toListModel data.1 := by
  rw [reinsertAux_eq]
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_update data.1 data.2 a (fun l => l.cons a b)
  exact h₂.trans (by simpa using h₁.symm)

theorem isHashSelf_foldl_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : AssocList α β) (target : { d : Array (AssocList α β) // 0 < d.size }) :
    IsHashSelf target.1 → IsHashSelf (l.foldl reinsertAux target).1 := by
  induction l generalizing target
  · simp [AssocList.foldl, AssocList.foldlM, Id.run]
  · next k v _ ih => exact fun h => ih _ (isHashSelf_reinsertAux _ _ _ h)

theorem toListModel_foldl_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : AssocList α β)
    (target : { d : Array (AssocList α β) // 0 < d.size }) :
    toListModel (l.foldl reinsertAux target).1 ~ l.toList ++ toListModel target.1 := by
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
      go (i + 1) (source.set ⟨i, h⟩ .nil) ((source.get ⟨i, h⟩).foldl reinsertAux target) := by
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

theorem toListModel_expand [BEq α] [Hashable α] [LawfulHashable α] [EquivBEq α] {buckets : {d : Array (AssocList α β) // 0 < d.size}} :
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

theorem toListModel_expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) :
    toListModel (expandIfNecessary m).1.2 ~ toListModel m.1.2 := by
  rw [expandIfNecessary]
  dsimp
  split
  · exact Perm.refl _
  · dsimp
    exact toListModel_expand

theorem WFImp.expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
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

theorem containsₘ_eq_containsKey [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α} :
    m.containsₘ a = (toListModel m.1.buckets).containsKey a := by
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.1.buckets hm.buckets_size a
  refine Eq.trans ?_ (List.containsKey_of_perm (hm.distinct.perm hl.symm) hl.symm)
  rw [containsₘ, AssocList.contains_eq, List.containsKey_append_of_not_contains_right]
  exact hlk hm.buckets_hash_self _ rfl

theorem findEntry?ₘ_eq_findEntry? [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.WFImp) (a : α) :
    findEntry?ₘ m a = (toListModel m.1.buckets).findEntry? a := by
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.1.buckets m.2 a
  refine Eq.trans ?_ (List.findEntry?_of_perm (h.distinct.perm hl.symm) hl.symm)
  rw [findEntry?ₘ, AssocList.findEntry?_eq, findEntry?_append_of_containsKey_eq_false]
  exact hlk h.buckets_hash_self _ rfl

/-! # `replaceₘ` -/

theorem toListModel_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : toListModel (m.replaceₘ a b).1.buckets ~ (toListModel m.1.2).replaceEntry a b := by
  rw [replaceₘ]
  dsimp only
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_update m.1.buckets m.2 a (fun l => l.replace a b)
  refine h₂.trans (Perm.trans ?_ (replaceEntry_of_perm _ _ h.distinct h₁).symm)
  rw [AssocList.toList_replace, replaceEntry_append_of_containsKey_right_eq_false]
  apply h₃ h.buckets_hash_self _ rfl

theorem isHashSelf_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : IsHashSelf (m.replaceₘ a b).1.buckets := by
  rw [replaceₘ]
  dsimp only
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  exact Or.inl (by simpa using containsKey_of_mem hp)

theorem wfImp_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : (m.replaceₘ a b).1.WFImp where
  buckets_hash_self := isHashSelf_replaceₘ m h a b
  buckets_size := by simpa [replaceₘ] using h.buckets_size
  size_eq := h.size_eq.trans (Eq.trans length_replaceEntry.symm (toListModel_replaceₘ _ h _ _).length_eq.symm)
  distinct := h.distinct.replaceEntry.perm (toListModel_replaceₘ _ h _ _)

/-! # `insertₘ` -/

theorem toListModel_consₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (a : α) (b : β a) : toListModel (m.consₘ a b).1.buckets ~ ⟨a, b⟩ :: (toListModel m.1.2) := by
  rw [consₘ]
  dsimp only
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_update m.1.buckets m.2 a (fun l => l.cons a b)
  refine h₂.trans (Perm.trans ?_ (Perm.cons _ h₁.symm))
  rw [AssocList.toList_cons, cons_append]

theorem isHashSelf_consₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : IsHashSelf (m.consₘ a b).1.buckets := by
  rw [consₘ]
  dsimp only
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
    refine Eq.trans ?_ (toListModel_consₘ _ _ _).length_eq.symm
    simpa [consₘ] using h.size_eq
  distinct := by
    refine (h.distinct.cons ?_).perm (toListModel_consₘ _ _ _)
    rwa [← containsₘ_eq_containsKey h]

theorem toListModel_insertₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : toListModel (m.insertₘ a b).1.2 ~ (toListModel m.1.2).insertEntry a b := by
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
    exact toListModel_consₘ m a b

theorem wfImp_insertₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.WFImp) (a : α) (b : β a) : (m.insertₘ a b).1.WFImp := by
  rw [insertₘ]
  split
  · apply wfImp_replaceₘ _ h
  · apply Raw₀.WFImp.expandIfNecessary
    apply wfImp_consₘ _ h _ _ (by simp_all)

end Raw₀

theorem Raw.WF.out [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw α β} (h : m.WF) : m.WFImp := by
  induction h
  · assumption
  · exact Raw₀.wfImp_empty
  · rw [Raw₀.insert_eq_insertₘ]
    exact Raw₀.wfImp_insertₘ _ (by simpa) _ _

end MyLean.DHashMap
