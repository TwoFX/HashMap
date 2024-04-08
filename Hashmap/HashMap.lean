/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.AssocList.Map
import Hashmap.LawfulHashable
import Std.Data.Array.Lemmas

namespace MyLean

namespace HashMap.Imp

def Buckets (α : Type u) [BEq α] (β : α → Type v) :=
  { t : Array (AssocListMap α β) // t.size.isPowerOfTwo }

namespace Buckets

def update [BEq α] (b : Buckets α β) (i : Fin b.1.size) (l : AssocListMap α β) : Buckets α β :=
  ⟨b.1.set i l, by simpa using b.2⟩

@[simp]
theorem update_size [BEq α] {b : Buckets α β} (i : Fin b.1.size) {l : AssocListMap α β} :
    (b.update i l).1.size = b.1.size := by simp [update]

theorem update_get [BEq α] {b : Buckets α β} {i : Fin b.1.size} {l : AssocListMap α β}
    {j : Fin (b.update i l).1.size}:
    (b.update i l).1[j] = if (i : Nat) = j then l else b.1[j] := by
  simp [update]
  rw [Array.get_set]

structure BucketWFAt [BEq α] [Hashable α] (l : AssocListMap α β)
    (size i : Nat) : Prop where
  hash_valid [LawfulHashable α] : ∀ a, l.contains a → (hash a % size).toNat = i

theorem BucketWFAt_nil [BEq α] [Hashable α] {size i : Nat} :
    BucketWFAt (AssocListMap.nil : AssocListMap α β) size i where
  hash_valid a h := by simp at h

theorem BucketWFAt_erase [BEq α] [EquivBEq α] [Hashable α] {l : AssocListMap α β} {k : α} {size i : Nat} :
    BucketWFAt l size i → BucketWFAt (l.erase k) size i :=
  fun ⟨h⟩ => ⟨fun a h' => h a <| l.contains_of_contains_erase h'⟩

theorem BucketWFAt_insert [BEq α] [EquivBEq α] [Hashable α] {l : AssocListMap α β} {k : α} {v : β k} {size i : Nat}
    (h : (hash k % size).toNat = i) : BucketWFAt l size i → BucketWFAt (l.insert k v) size i := by
  refine fun ⟨h⟩ => ⟨fun a h' => ?_⟩
  rw [l.contains_insert, Bool.or_eq_true] at h'
  rcases h' with (h'|h')
  · rwa [← hash_eq_of_beq h']
  · exact h _ h'

structure WF [BEq α] [Hashable α] [LawfulHashable α] (b : Buckets α β) : Prop where
  bucket_wf : ∀ (i : Fin b.1.size), BucketWFAt b.1[i] b.1.size i

theorem WF_update [BEq α] [Hashable α] [LawfulHashable α] {b : Buckets α β} {i : Fin b.1.size}
    {l : AssocListMap α β} : b.WF → BucketWFAt l b.1.size i → (b.update i l).WF := by
  refine fun ⟨h₁⟩ h₂ => ⟨fun j => ?_⟩
  rw [update_get]
  by_cases h' : i.1 = j
  · simpa [h'] using h₂
  · simp [h']
    apply h₁ (Fin.cast (by simp) j)

end Buckets

end HashMap.Imp

end MyLean
