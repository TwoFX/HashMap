/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic
import Hashmap.DHashMap.ForUpstream

/-!
In this file we define functions for manipulating a hash map based on operations defined in terms of their buckets.
Then we give "model implementations" of the hash map operations in terms of the basic building blocks and show that
the actual operations are equal to the model implementations. This means that later we will be able to prove properties
of the operations by proving general facts about the basic building blocks.
-/

set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v}

namespace MyLean.DHashMap

/-! # Setting up the infrastructure -/

def bucket [Hashable α] (self : Array (AssocList α β)) (h : 0 < self.size) (k : α) : AssocList α β :=
  let ⟨i, h⟩ := mkIdx (hash k) h
  self[i]

def updateBucket [Hashable α] (self : Array (AssocList α β)) (h : 0 < self.size) (k : α)
    (f : AssocList α β → AssocList α β) : Array (AssocList α β) :=
  let ⟨i, h⟩ := mkIdx (hash k) h
  self.uset i (f self[i]) h

@[simp]
theorem size_updateBucket [Hashable α] {self : Array (AssocList α β)} {h : 0 < self.size} {k : α}
    {f : AssocList α β → AssocList α β} : (updateBucket self h k f).size = self.size := by
  simp [updateBucket]

open List

theorem exists_bucket_of_uset [BEq α] [Hashable α]
  (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) (d : AssocList α β) :
    ∃ l, toListModel self ~ self[i.toNat].toList ++ l ∧
      toListModel (self.uset i d hi) ~ d.toList ++ l ∧
      (∀ [LawfulHashable α], IsHashSelf self →
        ∀ k : α, (mkIdx (hash k) (show 0 < self.size by omega)).1.toNat = i.toNat → l.containsKey k = false) := by
  have h₀ : 0 < self.size := by omega
  obtain ⟨l₁, l₂, h₁, h₂, h₃⟩ := Array.exists_of_update self i d hi
  refine ⟨l₁.bind AssocList.toList ++ l₂.bind AssocList.toList, ?_, ?_, ?_⟩
  · rw [toListModel, h₁]
    simpa using List.perm_append_comm_assoc _ _ _
  · rw [toListModel, h₃]
    simpa using List.perm_append_comm_assoc _ _ _
  · intro _ h k
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
      (∀ [LawfulHashable α], IsHashSelf m → ∀ k', hash k = hash k' → l.containsKey k' = false) := by
  let idx := mkIdx (hash k) h
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_uset m idx.1 idx.2 (f m[idx.1])
  exact ⟨l, h₁, h₂, fun h k' hk' => h₃ h _ (hk' ▸ rfl)⟩

theorem exists_bucket' [BEq α] [Hashable α]
    (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) :
      ∃ l, self.data.bind AssocList.toList ~ self[i.toNat].toList ++ l ∧
        (∀ [LawfulHashable α], IsHashSelf self → ∀ k,
          (mkIdx (hash k) (show 0 < self.size by omega)).1.toNat = i.toNat → l.containsKey k = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_uset self i hi .nil
  exact ⟨l, h₁, h₂⟩

theorem exists_bucket [BEq α] [Hashable α]
    (m : Array (AssocList α β)) (h : 0 < m.size) (k : α) :
    ∃ l : List (Σ a, β a), toListModel m ~ (bucket m h k).toList ++ l ∧
      (∀ [LawfulHashable α], IsHashSelf m → ∀ k', hash k = hash k' → l.containsKey k' = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_update m h k (fun _ => .nil)
  exact ⟨l, h₁, h₂⟩

namespace Raw₀

/-! # Definition of model functions -/

def replaceₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size, updateBucket m.1.buckets m.2 a (fun l => l.replace a b)⟩, by simpa using m.2⟩

def consₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size + 1, updateBucket m.1.buckets m.2 a (fun l => l.cons a b)⟩, by simpa using m.2⟩

def findEntry?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (Σ a, β a) :=
  (bucket m.1.buckets m.2 a).findEntry? a

def containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  (bucket m.1.buckets m.2 a).contains a

def insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  if m.containsₘ a then m.replaceₘ a b else Raw₀.expandIfNecessary (m.consₘ a b)

section

variable {β : Type v}

def find?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  (bucket m.1.buckets m.2 a).find? a

end

/-! # Equivalence between model functions and real implementations -/

theorem reinsertAux_eq [Hashable α] (data : { d : Array (AssocList α β) // 0 < d.size }) (a : α) (b : β a) :
    (reinsertAux data a b).1 = updateBucket data.1 data.2 a (fun l => l.cons a b) := rfl

theorem findEntry?_eq_findEntry?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    findEntry? m a = findEntry?ₘ m a := rfl

theorem contains_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    m.contains a = m.containsₘ a := rfl

theorem insert_eq_insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (insert m a b).1 = insertₘ m a b := by
  rw [insert, insertₘ, containsₘ, bucket]
  apply Subtype.eq
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> rfl

section

variable {β : Type v}

theorem find?_eq_find?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) :
    m.find? a = m.find?ₘ a := rfl

end

end Raw₀

end MyLean.DHashMap
