/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic

/-!
In this file we define functions for manipulating a hash map based on operations defined in terms of their buckets.
Then we give "model implementations" of the hash map operations in terms of the basic building blocks and show that
the actual operations are equal to the model implementations. This means that later we will be able to prove properties
of the operations by proving general facts about the basic building blocks.
-/

set_option autoImplicit false

universe u v

variable {α : Type v} {β : α → Type v}

namespace MyLean.DHashMap

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

namespace Model

def replace [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size, updateBucket m.1.buckets m.2 a (fun l => l.replace a b)⟩, by simpa using m.2⟩

def cons [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size + 1, updateBucket m.1.buckets m.2 a (fun l => l.cons a b)⟩, by simpa using m.2⟩

def insert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  if (bucket m.1.buckets m.2 a).contains a then replace m a b else Raw₀.expandIfNecessary (cons m a b)

def findEntry? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (Σ a, β a) :=
  (bucket m.1.buckets m.2 a).findEntry? a

end Model

namespace Raw₀

theorem reinsertAux_eq [Hashable α] (data : { d : Array (AssocList α β) // 0 < d.size }) (a : α) (b : β a) :
    (reinsertAux data a b).1 = updateBucket data.1 data.2 a (fun l => l.cons a b) := rfl

theorem insert_eq_model [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (insert m a b).1 = Model.insert m a b := by
  rw [insert, Model.insert, bucket]
  apply Subtype.eq
  dsimp
  split
  · rfl
  · rfl

theorem findEntry?_eq_model [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    findEntry? m a = Model.findEntry? m a := rfl

end Raw₀

end MyLean.DHashMap
