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

/-! # Setting up the infrastructure -/

theorem exists_bucket_of_uset [BEq α] [Hashable α]
  (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) (d : AssocList α β) :
    ∃ l, toListModel self ~ self[i.toNat].toList ++ l ∧
      toListModel (self.uset i d hi) ~ d.toList ++ l ∧
      (∀ [EquivBEq α] [LawfulHashable α],
        IsHashSelf self → ∀ k : α, (mkIdx (hash k) (show 0 < self.size by omega)).1.toNat = i.toNat → l.containsKey k = false) := by
  have h₀ : 0 < self.size := by omega
  obtain ⟨l₁, l₂, h₁, h₂, h₃⟩ := Array.exists_of_update self i d hi
  refine ⟨l₁.bind AssocList.toList ++ l₂.bind AssocList.toList, ?_, ?_, ?_⟩
  · rw [toListModel, h₁]
    simpa using List.perm_append_comm_assoc _ _ _
  · rw [toListModel, h₃]
    simpa using List.perm_append_comm_assoc _ _ _
  · intro _ _ h k
    rw [← Decidable.not_imp_not]
    intro hk
    simp only [Bool.not_eq_false, containsKey_eq_true_iff_exists_mem, mem_append, mem_bind] at hk
    obtain ⟨⟨k', v'⟩, ⟨(⟨a, ha₁, ha₂⟩|⟨a, ha₁, ha₂⟩), hk⟩⟩ := hk
    · obtain ⟨n, hn⟩ := List.get_of_mem ha₁
      rw [List.get_eq_get_append_right (self[i] :: l₂)] at hn
      suffices (mkIdx (hash k') h₀).1.toNat = n from
        Nat.ne_of_lt (Nat.lt_of_eq_of_lt (hash_eq hk ▸ this) (h₂ ▸ n.2))
      rw [List.get_congr h₁.symm, ← Array.getElem_eq_data_get] at hn
      exact (h.hashes_to n (by omega)).hash_self h₀ _ (hn.symm ▸ ha₂)
    · obtain ⟨n, hn⟩ := List.get_of_mem ha₁
      rw [List.get_eq_get_cons self[i], List.get_eq_get_append_left l₁] at hn
      suffices (mkIdx (hash k') h₀).1.toNat = n + 1 + l₁.length by
        refine Nat.ne_of_lt' ?_
        simp only [← hash_eq hk, this, h₂, Nat.lt_add_left_iff_pos, Nat.succ_pos]
      rw [List.get_congr h₁.symm, ← Array.getElem_eq_data_get] at hn
      refine (h.hashes_to (n + 1 + l₁.length) ?_).hash_self h₀ _ (hn.symm ▸ ha₂)
      rw [Array.size_eq_length_data, h₁, length_append, length_cons]
      omega

theorem exists_bucket_of_update [BEq α] [Hashable α] (m : Array (AssocList α β)) (h : 0 < m.size) (k : α)
    (f : AssocList α β → AssocList α β) :
    ∃ l : List (Σ a, β a),
      toListModel m ~ (bucket m h k).toList ++ l ∧
      toListModel (updateBucket m h k f) ~ (f (bucket m h k)).toList ++ l ∧
      (∀ [EquivBEq α] [LawfulHashable α], IsHashSelf m → ∀ k', hash k = hash k' → l.containsKey k' = false) := by
  let idx := mkIdx (hash k) h
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_uset m idx.1 idx.2 (f m[idx.1])
  exact ⟨l, h₁, h₂, fun h k' hk' => h₃ h _ (hk' ▸ rfl)⟩

theorem exists_bucket' [BEq α] [Hashable α]
    (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) :
      ∃ l, self.data.bind AssocList.toList ~ self[i.toNat].toList ++ l ∧
        (∀ [EquivBEq α] [LawfulHashable α], IsHashSelf self → ∀ k,
          (mkIdx (hash k) (show 0 < self.size by omega)).1.toNat = i.toNat → l.containsKey k = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_uset self i hi .nil
  exact ⟨l, h₁, h₂⟩

theorem exists_bucket [BEq α] [Hashable α]
    (m : Array (AssocList α β)) (h : 0 < m.size) (k : α) :
    ∃ l : List (Σ a, β a), toListModel m ~ (bucket m h k).toList ++ l ∧
      (∀ [EquivBEq α] [LawfulHashable α], IsHashSelf m → ∀ k', hash k = hash k' → l.containsKey k' = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_update m h k (fun _ => .nil)
  exact ⟨l, h₁, h₂⟩

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

@[simp]
theorem size_empty {c} : (empty c : Raw₀ α β).1.size = 0 := rfl

@[simp]
theorem toListModel_buckets_empty {c} : toListModel (empty c : Raw₀ α β).1.buckets = [] :=
  toListModel_mkArray_nil

theorem ActuallyWF.empty [BEq α] [Hashable α] {c} : (empty c : Raw₀ α β).1.ActuallyWF where
  buckets_hash_self := by simp [Raw.empty, Raw₀.empty]
  buckets_size := (Raw.WF.empty _).size_buckets_pos
  size_eq := by simp
  distinct := by simp

theorem reinsertAux_hashSelf [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) (h : IsHashSelf data.1) :
    IsHashSelf (reinsertAux data a b).1 := by
  rw [reinsertAux_eq]
  refine h.updateBucket (fun l p hp => ?_)
  simp only [AssocList.toList_cons, mem_cons] at hp
  rcases hp with (rfl|hp)
  · exact Or.inr rfl
  · exact Or.inl (containsKey_of_mem hp)

theorem reinsertAux_toListModel [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) :
    toListModel (reinsertAux data a b).1 ~ ⟨a, b⟩ :: toListModel data.1 := by
  rw [reinsertAux_eq]
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_update data.1 data.2 a (fun l => l.cons a b)
  exact h₂.trans (by simpa using h₁.symm)

theorem expand.foldl_hashSelf [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : AssocList α β) (target : { d : Array (AssocList α β) // 0 < d.size }) :
    IsHashSelf target.1 → IsHashSelf (l.foldl reinsertAux target).1 := by
  induction l generalizing target
  · simp [AssocList.foldl, AssocList.foldlM, Id.run]
  · next k v _ ih => exact fun h => ih _ (reinsertAux_hashSelf _ _ _ h)

theorem expand.foldl_toListModel [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : AssocList α β)
    (target : { d : Array (AssocList α β) // 0 < d.size }) :
    toListModel (l.foldl reinsertAux target).1 ~ l.toList ++ toListModel target.1 := by
  induction l generalizing target
  · simp
  · next k v t ih =>
    skip
    simp at ih
    simp
    refine (ih _).trans ?_
    refine ((reinsertAux_toListModel _ _ _).append_left _).trans perm_middle

theorem expand.go_pos [Hashable α] {i : Nat} {source : Array (AssocList α β)} {target : { d : Array (AssocList α β) // 0 < d.size }}
    (h : i < source.size) : expand.go i source target =
      go (i + 1) (source.set ⟨i, h⟩ .nil) ((source.get ⟨i, h⟩).foldl reinsertAux target) := by
  rw [expand.go]
  simp only [h, dite_true]

theorem expand.go_neg [Hashable α] {i : Nat} {source : Array (AssocList α β)} {target : { d : Array (AssocList α β) // 0 < d.size}}
    (h : ¬i < source.size) : expand.go i source target = target := by
  rw [expand.go]
  simp only [h, dite_false]

theorem expand.hashSelf [BEq α] [Hashable α] [LawfulHashable α] [EquivBEq α] {buckets : {d : Array (AssocList α β) // 0 < d.size}} :
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
        exact expand.foldl_hashSelf _ _
      · next i source target hi =>
        rw [expand.go_neg hi]
        exact id

theorem expand_toListModel [BEq α] [Hashable α] [LawfulHashable α] [EquivBEq α] {buckets : {d : Array (AssocList α β) // 0 < d.size}} :
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
        refine ((expand.foldl_toListModel _ _).append_left _).trans ?_
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
    exact expand_toListModel

theorem ActuallyWF.expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) : (expandIfNecessary m).1.ActuallyWF := by
  rw [Raw₀.expandIfNecessary]
  dsimp
  split
  · exact h
  · let ⟨⟨size, buckets⟩, hm⟩ := m
    have := expand_toListModel (buckets := ⟨buckets, hm⟩)
    dsimp at this
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using expand.hashSelf
    · simpa using (expand _).2
    · refine h.size_eq.trans ?_
      simpa using this.symm.length_eq
    · simpa using WF_of_perm this h.distinct

end Raw₀

namespace Model

theorem toListModel_replace [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) (a : α) (b : β a) : toListModel (replace m a b).1.buckets ~ (toListModel m.1.2).replaceEntry a b := by
  rw [replace]
  dsimp only
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_update m.1.buckets m.2 a (fun l => l.replace a b)
  refine h₂.trans (Perm.trans ?_ (replaceEntry_of_perm _ _ h.distinct h₁).symm)
  rw [AssocList.toList_replace, replaceEntry_append_of_containsKey_right_eq_false]
  apply h₃ h.buckets_hash_self _ rfl

theorem isHashSelf_replace [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) (a : α) (b : β a) : IsHashSelf (replace m a b).1.buckets := by
  rw [replace]
  dsimp only
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  exact Or.inl (by simpa using containsKey_of_mem hp)

theorem ActuallyWF_replace [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) (a : α) (b : β a) : (replace m a b).1.ActuallyWF where
  buckets_hash_self := isHashSelf_replace m h a b
  buckets_size := by simpa [replace] using h.buckets_size
  size_eq := h.size_eq.trans (Eq.trans length_replaceEntry.symm (toListModel_replace _ h _ _).length_eq.symm)
  distinct := WF_of_perm (toListModel_replace _ h _ _) (WF_replaceEntry h.distinct)

theorem toListModel_cons [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : { m : Raw α β // 0 < m.buckets.size }) (a : α) (b : β a) :
    toListModel (cons m a b).1.buckets ~ ⟨a, b⟩ :: (toListModel m.1.2) := by
  rw [cons]
  dsimp only
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_update m.1.buckets m.2 a (fun l => l.cons a b)
  refine h₂.trans (Perm.trans ?_ (Perm.cons _ h₁.symm))
  rw [AssocList.toList_cons, cons_append]

theorem isHashSelf_cons [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) (a : α) (b : β a) : IsHashSelf (cons m a b).1.buckets := by
  rw [cons]
  dsimp only
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  simp only [AssocList.toList_cons, mem_cons] at hp
  rcases hp with (rfl|hp)
  · exact Or.inr rfl
  · exact Or.inl (containsKey_of_mem hp)

-- TODO: as stated, this is in the wrong namespace
theorem bucket_contains_eq_containsKey [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw α β} (hm : m.ActuallyWF) {a : α} :
    (bucket m.buckets hm.buckets_size a).contains a = (toListModel m.buckets).containsKey a := by
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.buckets hm.buckets_size a
  refine Eq.trans ?_ (List.containsKey_of_perm (WF_of_perm hl.symm hm.distinct) hl.symm)
  rw [AssocList.contains_eq, List.containsKey_append_of_not_contains_right]
  exact hlk hm.buckets_hash_self _ rfl

theorem ActuallyWF_cons [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) (a : α) (b : β a) (hc : (bucket m.1.buckets m.2 a).contains a = false) : (cons m a b).1.ActuallyWF where
  buckets_hash_self := isHashSelf_cons m h a b
  buckets_size := by simpa [cons] using h.buckets_size
  size_eq := by
    refine Eq.trans ?_ (toListModel_cons _ _ _).length_eq.symm
    simpa [cons] using h.size_eq
  distinct := by
    refine WF_of_perm (toListModel_cons _ _ _) (WF_cons ?_ h.distinct)
    rwa [← bucket_contains_eq_containsKey h]

theorem toListModel_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) (a : α) (b : β a) : toListModel (insert m a b).1.2 ~ (toListModel m.1.2).insertEntry a b := by
  rw [insert]
  split
  · next h' =>
    rw [bucket_contains_eq_containsKey h] at h'
    rw [insertEntry_of_containsKey h']
    exact toListModel_replace _ h _ _
  · next h' =>
    rw [bucket_contains_eq_containsKey h, Bool.not_eq_true] at h'
    rw [insertEntry_of_containsKey_eq_false h']
    refine (Raw₀.toListModel_expandIfNecessary _).trans ?_
    exact toListModel_cons m a b

theorem ActuallyWF_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : m.1.ActuallyWF) (a : α) (b : β a) : (insert m a b).1.ActuallyWF := by
  rw [insert]
  split
  · apply ActuallyWF_replace _ h
  · apply Raw₀.ActuallyWF.expandIfNecessary
    apply ActuallyWF_cons _ h _ _ (by simp_all)

theorem findEntry?_eq_findEntry? [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α β) (h : m.1.ActuallyWF) (a : α) :
    Model.findEntry? m a = (toListModel m.1.buckets).findEntry? a := by
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.1.buckets m.2 a
  refine Eq.trans ?_ (List.findEntry?_of_perm (WF_of_perm hl.symm h.distinct) hl.symm)
  rw [Model.findEntry?, AssocList.findEntry?_eq, findEntry?_append_of_containsKey_eq_false]
  exact hlk h.buckets_hash_self _ rfl

end Model

theorem Raw.WF.out [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw α β} (h : m.WF) : m.ActuallyWF := by
  induction h
  · assumption
  · exact Raw₀.ActuallyWF.empty
  · rw [Raw₀.insert_eq_model]
    exact Model.ActuallyWF_insert _ (by simpa) _ _


end MyLean.DHashMap
