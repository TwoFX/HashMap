/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic

set_option autoImplicit false

universe u v

variable {α : Type v} {β : α → Type v}

open List

-- TODO
theorem List.perm_append_comm_assoc (l₁ l₂ l₃ : List α) : l₁ ++ (l₂ ++ l₃) ~ l₂ ++ (l₁ ++ l₃) := by
  simpa only [List.append_assoc] using perm_append_comm.append_right _

namespace MyLean.DHashMap

-- TODO: this is just about arrays
theorem Array.exists_of_update (self : Array (AssocList α β)) (i d h) :
    ∃ l₁ l₂, self.data = l₁ ++ self[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (self.uset i d h).data = l₁ ++ d :: l₂ := by
  simp [Array.getElem_eq_data_get]; exact List.exists_of_set' _

-- TODO
theorem List.length_le_append_right {l₁ l₂ : List α} : l₁.length ≤ (l₁ ++ l₂).length := by
  simpa using Nat.le_add_right _ _

-- TODO
theorem List.length_le_append_left {l₁ l₂ : List α} : l₂.length ≤ (l₁ ++ l₂).length := by
  simpa using Nat.le_add_left _ _

-- TODO
theorem List.get_eq_get_append_right {l₁ : List α} (l₂ : List α) {n : Fin l₁.length} :
    l₁.get n = (l₁ ++ l₂).get (n.castLE length_le_append_right) := by
  rw [get_append]; rfl

-- TODO
theorem List.get_eq_get_append_left (l₁ : List α) {l₂ : List α} {n : Fin l₂.length} :
    l₂.get n = (l₁ ++ l₂).get ((n.addNat l₁.length).cast (by simp [Nat.add_comm l₂.length])) := by
  rw [get_append_right]
  · simp
  · simpa using Nat.le_add_left _ _
  · simp

-- TODO
theorem List.get_eq_get_cons (a : α) {l : List α} {n : Fin l.length} :
    l.get n = (a :: l).get ((n.addNat 1).cast (by simp)) := by
  erw [get_cons_succ]

-- TODO
theorem List.get_congr {l₁ l₂ : List α} {n : Fin l₁.length} (h : l₁ = l₂) :
    l₁.get n = l₂.get (n.cast (h ▸ rfl)) := by
  cases h; rfl

-- TODO
theorem Nat.lt_of_eq_of_lt {n m k : Nat} : n = m → m < k → n < k :=
  fun h₁ h₂ => h₁ ▸ h₂

theorem exists_bucket_of_uset [BEq α] [Hashable α]
  (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) (d : AssocList α β) :
    ∃ l, self.data.bind AssocList.toList ~ self[i.toNat].toList ++ l ∧
      (self.uset i d hi).data.bind AssocList.toList ~ d.toList ++ l ∧
      (∀ [EquivBEq α] [LawfulHashable α],
        IsHashSelf self → ∀ k : α, ((hash k).toUSize % self.size).toNat = i.toNat → l.containsKey k = false) := by
  obtain ⟨l₁, l₂, h₁, h₂, h₃⟩ := Array.exists_of_update self i d hi
  refine ⟨l₁.bind AssocList.toList ++ l₂.bind AssocList.toList, ?_, ?_, ?_⟩
  · rw [h₁]
    simpa using List.perm_append_comm_assoc _ _ _
  · rw [h₃]
    simpa using List.perm_append_comm_assoc _ _ _
  · intro _ _ h k
    rw [← Decidable.not_imp_not]
    intro hk
    simp only [Bool.not_eq_false, containsKey_eq_true_iff_exists_mem, mem_append, mem_bind] at hk
    obtain ⟨⟨k', v'⟩, ⟨(⟨a, ha₁, ha₂⟩|⟨a, ha₁, ha₂⟩), hk⟩⟩ := hk
    · obtain ⟨n, hn⟩ := List.get_of_mem ha₁
      rw [List.get_eq_get_append_right (self[i] :: l₂)] at hn
      suffices ((hash k').toUSize % self.size).toNat = n from
        Nat.ne_of_lt (Nat.lt_of_eq_of_lt (hash_eq hk ▸ this) (h₂ ▸ n.2))
      rw [List.get_congr h₁.symm, ← Array.getElem_eq_data_get] at hn
      exact (h.hashes_to n (by omega)).hash_self _ (hn.symm ▸ ha₂)
    · obtain ⟨n, hn⟩ := List.get_of_mem ha₁
      rw [List.get_eq_get_cons self[i], List.get_eq_get_append_left l₁] at hn
      suffices ((hash k').toUSize % self.size).toNat = n + 1 + l₁.length from
        Nat.ne_of_lt' (h₂ ▸ ((hash_eq hk ▸ this) ▸ by omega))
      rw [List.get_congr h₁.symm, ← Array.getElem_eq_data_get] at hn
      refine (h.hashes_to (n + 1 + l₁.length) ?_).hash_self _ (hn.symm ▸ ha₂)
      rw [Array.size_eq_length_data, h₁, length_append, length_cons]
      omega

theorem exists_bucket [BEq α] [Hashable α]
    (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) :
      ∃ l, self.data.bind AssocList.toList ~ self[i.toNat].toList ++ l ∧
        (∀ [EquivBEq α] [LawfulHashable α], IsHashSelf self → ∀ k,
          ((hash k).toUSize % self.size).toNat = i.toNat → l.containsKey k = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_uset self i hi .nil
  exact ⟨l, h₁, h₂⟩

namespace Raw

@[simp]
theorem toList_empty {c} : (empty c : Raw α β).toList = [] := by
  suffices ∀ d, (List.replicate d AssocList.nil).bind AssocList.toList = [] from this _
  intro d
  induction d <;> simp_all

theorem findEntry?WellFormed_eq_findEntry_toList [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : { m : Raw α β // 0 < m.buckets.size }) (h : m.1.WF) (a : α) :
      Raw.findEntry?WellFormed m a = m.1.toList.findEntry? a := by
  rw [findEntry?WellFormed]
  dsimp only [Array.ugetElem_eq_getElem]
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.1.buckets (mkIdx (hash a) m.2).1 (mkIdx (hash a) m.2).2
  refine Eq.trans ?_ (List.findEntry?_of_perm (WF_of_perm hl.symm h.distinct) hl.symm)
  rw [AssocList.findEntry?_eq, findEntry?_append_of_containsKey_eq_false]
  exact hlk h.buckets_hash_self _ rfl

end Raw

end MyLean.DHashMap
