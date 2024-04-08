/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.AssocList.Map
import Hashmap.LawfulHashable

namespace Lean

namespace HashMap.Imp

def Buckets (α : Type u) [BEq α] (β : α → Type v) :=
  { t : Array (AssocListMap α β) // t.size.isPowerOfTwo }

namespace Buckets

def update [BEq α] (b : Buckets α β) (i : USize) (h : i.toNat < b.1.size) (l : AssocListMap α β) : Buckets α β :=
  ⟨b.1.uset i l h, by simpa using b.2⟩

@[simp]
theorem update_size [BEq α] {b : Buckets α β} {i : USize} {h : i.toNat < b.1.size} {l : AssocListMap α β} :
    (b.update i h l).1.size = b.1.size := by simp [update]

-- Todo: this is insane
macro_rules
| `(tactic| get_elem_tactic_trivial) => `(tactic| simpa)

theorem update_get [BEq α] {b : Buckets α β} {i : USize} {h : i.toNat < b.1.size} {l : AssocListMap α β}
    {j : USize} {hj : j.toNat < b.1.size} :
    (b.update i h l).1[j] = if i = j then l else b.1[j] := by
  sorry -- Meh

structure BucketWFAt [BEq α] [Hashable α] [LawfulHashable α] (l : AssocListMap α β)
    (size : Nat) (index : USize) : Prop where
  hash_valid : ∀ a, l.contains a → (hash a % size).toNat = i

structure WF [BEq α] [Hashable α] [LawfulHashable α] (b : Buckets α β) : Prop where
  bucket_wf : ∀ (i : USize) (h : i.toNat < b.1.size), BucketWFAt b.1[i] b.1.size i

theorem WF_update [BEq α] [Hashable α] [LawfulHashable α] {b : Buckets α β} {i : USize} {h : i.toNat < b.1.size}
    {l : AssocListMap α β} : b.WF → BucketWFAt l b.1.size i → (b.update i h l).WF := by
  refine fun ⟨h₁⟩ h₂ => ⟨fun j hj => ?_⟩
  rw [update_get]
  by_cases h' : i = j
  · simpa [h'] using h₂
  · simp [h']
    apply h₁ j
  · simpa using hj

end Buckets

end HashMap.Imp

end Lean
