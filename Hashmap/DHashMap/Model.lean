/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic
import Hashmap.DHashMap.ForUpstream
import Hashmap.Leftovers

/-!
In this file we define functions for manipulating a hash map based on operations defined in terms of their buckets.
Then we give "model implementations" of the hash map operations in terms of these basic building blocks and show that
the actual operations are equal to the model implementations. This means that later we will be able to prove properties
of the operations by proving general facts about the basic building blocks.
-/

set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

namespace MyLean.DHashMap

/-! # Setting up the infrastructure -/

def bucket [Hashable α] (self : Array (AssocList α β)) (h : 0 < self.size) (k : α) : AssocList α β :=
  let ⟨i, h⟩ := mkIdx self.size h (hash k)
  self[i]

def updateBucket [Hashable α] (self : Array (AssocList α β)) (h : 0 < self.size) (k : α)
    (f : AssocList α β → AssocList α β) : Array (AssocList α β) :=
  let ⟨i, h⟩ := mkIdx self.size h (hash k)
  self.uset i (f self[i]) h

def updateAllBuckets (self : Array (AssocList α β)) (f : AssocList α β → AssocList α δ) :
    Array (AssocList α δ) :=
  self.map f

def withComputedSize (self : Array (AssocList α β)) : Raw α β :=
  ⟨computeSize self, self⟩

@[simp]
theorem size_updateBucket [Hashable α] {self : Array (AssocList α β)} {h : 0 < self.size} {k : α}
    {f : AssocList α β → AssocList α β} : (updateBucket self h k f).size = self.size := by
  simp [updateBucket]

@[simp]
theorem size_updateAllBuckets {self : Array (AssocList α β)} {f : AssocList α β → AssocList α δ} :
    (updateAllBuckets self f).size = self.size := by
  simp [updateAllBuckets]

@[simp]
theorem buckets_size_withComputedSize {self : Array (AssocList α β)} :
    (withComputedSize self).2.size = self.size := by
  simp [withComputedSize]

@[simp]
theorem size_withComputedSize {self : Array (AssocList α β)} :
    (withComputedSize self).size = computeSize self := rfl

@[simp]
theorem buckets_withComputedSize {self : Array (AssocList α β)} :
    (withComputedSize self).buckets = self := rfl

open List

theorem exists_bucket_of_uset [BEq α] [Hashable α]
  (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) (d : AssocList α β) :
    ∃ l, toListModel self ~ self[i.toNat].toList ++ l ∧
      toListModel (self.uset i d hi) ~ d.toList ++ l ∧
      (∀ [LawfulHashable α], IsHashSelf self →
        ∀ k : α, (mkIdx self.size (by omega) (hash k)).1.toNat = i.toNat → l.containsKey k = false) := by
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
      suffices (mkIdx self.size h₀ (hash k')).1.toNat = n from
        Nat.ne_of_lt (Nat.lt_of_eq_of_lt (hash_eq hk ▸ this) (h₂ ▸ n.2))
      rw [List.get_congr h₁.symm, ← Array.getElem_eq_data_get] at hn
      exact (h.hashes_to n (by omega)).hash_self h₀ _ (hn.symm ▸ ha₂)
    · obtain ⟨n, hn⟩ := List.get_of_mem ha₁
      rw [List.get_eq_get_cons self[i], List.get_eq_get_append_left l₁] at hn
      suffices (mkIdx self.size h₀ (hash k')).1.toNat = n + 1 + l₁.length by
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
  let idx := mkIdx m.size h (hash k)
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_uset m idx.1 idx.2 (f m[idx.1])
  exact ⟨l, h₁, h₂, fun h k' hk' => h₃ h _ (hk' ▸ rfl)⟩

theorem exists_bucket' [BEq α] [Hashable α]
    (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) :
      ∃ l, self.data.bind AssocList.toList ~ self[i.toNat].toList ++ l ∧
        (∀ [LawfulHashable α], IsHashSelf self → ∀ k,
          (mkIdx self.size (by omega) (hash k)).1.toNat = i.toNat → l.containsKey k = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_uset self i hi .nil
  exact ⟨l, h₁, h₂⟩

theorem exists_bucket [BEq α] [Hashable α]
    (m : Array (AssocList α β)) (h : 0 < m.size) (k : α) :
    ∃ l : List (Σ a, β a), toListModel m ~ (bucket m h k).toList ++ l ∧
      (∀ [LawfulHashable α], IsHashSelf m → ∀ k', hash k = hash k' → l.containsKey k' = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_update m h k (fun _ => .nil)
  exact ⟨l, h₁, h₂⟩

/--
This is the general theorem used to show that access operations are correct.
-/
theorem apply_bucket [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α}
    {f : AssocList α β → γ} {g : List (Σ a, β a) → γ} (hfg : ∀ {l}, f l = g l.toList)
    (hg₁ : ∀ {l l'}, l.DistinctKeys → l ~ l' → g l = g l') (hg₂ : ∀ {l l'}, l'.containsKey a = false → g (l ++ l') = g l) :
    f (bucket m.1.buckets m.2 a) = g (toListModel m.1.buckets) := by
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.1.buckets hm.buckets_size a
  refine Eq.trans ?_ (hg₁ (hm.distinct.perm hl.symm) hl.symm)
  rw [hfg, hg₂]
  exact hlk hm.buckets_hash_self _ rfl

/--
This is the general theorem to show that modification operations are correct.
-/
theorem toListModel_updateBucket [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : m.1.WFImp) {a : α}
    {f : AssocList α β → AssocList α β} {g : List (Σ a, β a) → List (Σ a, β a)} (hfg : ∀ {l}, (f l).toList = g l.toList)
    (hg₁ : ∀ {l l'}, l.DistinctKeys → l ~ l' → g l ~ g l') (hg₂ : ∀ {l l'}, l'.containsKey a = false → g (l ++ l') = g l ++ l') :
    toListModel (updateBucket m.1.buckets m.2 a f) ~ g (toListModel m.1.2) := by
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_update m.1.buckets m.2 a f
  refine h₂.trans (Perm.trans ?_ (hg₁ hm.distinct h₁).symm)
  rw [hfg, hg₂]
  exact h₃ hm.buckets_hash_self _ rfl

-- TODO: clean up this proof
theorem toListModel_updateAllBuckets {m : Raw₀ α β} {f : AssocList α β → AssocList α δ} {g : List (Σ a, β a) → List (Σ a, δ a)}
    (hfg : ∀ {l}, (f l).toList ~ g l.toList) (hg : ∀ {l l'}, g (l ++ l') ~ g l ++ g l') :
    toListModel (updateAllBuckets m.1.buckets f) ~ g (toListModel m.1.2) := by
  have hg₀ : g [] = [] := by
    rw [← List.length_eq_zero]
    have := (hg (l := []) (l' := [])).length_eq
    rw [List.length_append, List.append_nil] at this
    omega
  rw [updateAllBuckets, toListModel, Array.map_data, List.bind_eq_foldl, List.foldl_map, toListModel, List.bind_eq_foldl]
  suffices ∀ (l : List (AssocList α β)) (l' : List (Σ a, δ a)) (l'' : List (Σ a, β a)), g l'' ~ l' →
      l.foldl (fun acc a => acc ++ (f a).toList) l' ~ g (l.foldl (fun acc a => acc ++ a.toList) l'') by
    simpa using this m.1.buckets.data [] [] (by simp [hg₀])
  rintro l l' l'' h
  induction l generalizing l' l''
  · simpa using h.symm
  · next l t ih =>
    simp only [foldl_cons]
    apply ih
    exact hg.trans (Perm.append h hfg.symm)

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

/--
This is the general theorem to show that modification operations preserve well-formedness of buckets.
-/
theorem updateBucket [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Array (AssocList α β)} {h : 0 < m.size} {a : α} {f : AssocList α β → AssocList α β}
    (hf : ∀ l p, p ∈ (f l).toList → l.toList.containsKey p.1 ∨ hash p.1 = hash a) (hm : IsHashSelf m) : IsHashSelf (updateBucket m h a f) := by
  rw [DHashMap.updateBucket]
  refine IsHashSelf.uset (fun h' => ⟨fun _ p hp => ?_⟩) hm
  rcases hf _ _ hp with (hf|hf)
  · rw [containsKey_eq_true_iff_exists_mem] at hf
    rcases hf with ⟨q, hq₁, hq₂⟩
    rw [← h'.hash_self h _ hq₁, hash_eq hq₂]
  · rw [hf]

theorem updateAllBuckets [BEq α] [Hashable α] [LawfulHashable α] {m : Array (AssocList α β)} {f : AssocList α β → AssocList α δ}
    (hf : ∀ l p, p ∈ (f l).toList → l.toList.containsKey p.1) (hm : IsHashSelf m) : IsHashSelf (updateAllBuckets m f) := by
  rw [DHashMap.updateAllBuckets]
  refine ⟨fun j hj => ?_⟩
  simp only [Array.getElem_map, Array.size_map]
  refine ⟨fun h p hp => ?_⟩
  rcases containsKey_eq_true_iff_exists_mem.1 (hf _ _ hp) with ⟨q, hq₁, hq₂⟩
  rw [← hash_eq hq₂, (hm.hashes_to _ _).hash_self _ _ hq₁]

end IsHashSelf

namespace Raw₀

/-! # Definition of model functions -/

def replaceₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size, updateBucket m.1.buckets m.2 a (fun l => l.replace a b)⟩, by simpa using m.2⟩

def consₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size + 1, updateBucket m.1.buckets m.2 a (fun l => l.cons a b)⟩, by simpa using m.2⟩

def findEntry?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (Σ a, β a) :=
  (bucket m.1.buckets m.2 a).findEntry? a

def find?ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  (bucket m.1.buckets m.2 a).findCast? a

def containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  (bucket m.1.buckets m.2 a).contains a

def insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  if m.containsₘ a then m.replaceₘ a b else Raw₀.expandIfNecessary (m.consₘ a b)

def eraseₘaux [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  ⟨⟨m.1.size - 1, updateBucket m.1.buckets m.2 a (fun l => l.erase a)⟩, by simpa using m.2⟩

def eraseₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  if m.containsₘ a then m.eraseₘaux a else m

def filterMapₘ (m : Raw₀ α β) (f : (a : α) → β a → Option (δ a)) : Raw₀ α δ :=
  ⟨withComputedSize (updateAllBuckets m.1.buckets fun l => l.filterMap f), by simpa using m.2⟩

def mapₘ (m : Raw₀ α β) (f : (a : α) → β a → δ a) : Raw₀ α δ :=
  ⟨⟨m.1.size, updateAllBuckets m.1.buckets (AssocList.map f)⟩, by simpa using m.2⟩

section

variable {β : Type v}

def findConst?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  (bucket m.1.buckets m.2 a).find? a

end

/-! # Equivalence between model functions and real implementations -/

theorem reinsertAux_eq [Hashable α] (data : { d : Array (AssocList α β) // 0 < d.size }) (a : α) (b : β a) :
    (reinsertAux hash data a b).1 = updateBucket data.1 data.2 a (fun l => l.cons a b) := rfl

theorem findEntry?_eq_findEntry?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    findEntry? m a = findEntry?ₘ m a := rfl

theorem find?_eq_find?ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    find? m a = find?ₘ m a := rfl

theorem contains_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    m.contains a = m.containsₘ a := rfl

theorem insert_eq_insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insert a b).1 = m.insertₘ a b := by
  rw [insert, insertₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> rfl

theorem erase_eq_eraseₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : m.erase a = m.eraseₘ a := by
  rw [erase, eraseₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> rfl

theorem filterMap_eq_filterMapₘ (m : Raw₀ α β) (f : (a : α) → β a → Option (δ a)) :
    m.filterMap f = m.filterMapₘ f := rfl

theorem map_eq_mapₘ (m : Raw₀ α β) (f : (a : α) → β a → δ a) :
    m.map f = m.mapₘ f := rfl

section

variable {β : Type v}

theorem findConst?_eq_findConst?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) :
    m.findConst? a = m.findConst?ₘ a := rfl

end

end Raw₀

end MyLean.DHashMap
