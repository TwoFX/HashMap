/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic

set_option autoImplicit false

universe u v w

variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v} (γ : Type v) (δ : α → Type w) (ε : Type w)

namespace MyLean.DHashMap.Ops

section modification

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
Returns the previous mapping if there was one.
-/
def insert₁ (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Option (Σ a, β a) :=
  sorry

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
Returns the previous mapping if there was one.
-/
def insert₂ (m : DHashMap α (fun _ => γ)) (a : α) (b : γ) : DHashMap α (fun _ => γ) × Option γ :=
  sorry

/--
Inserts the mapping into the map, but does not alter the map if there is already a mapping.
-/
def insertIfNew (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  sorry

/--
Inserts the mapping into the map, but does not alter the map if there is already a mapping.
Returns `true` if the map was altered.
-/
def insertIfNew' (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  sorry

/--
Inserts the mapping into the map, but does not alter the map if there is already a mapping.
Returns the existing mapping if there is one, or `none` if the given mapping was inserted.
-/
def insertIfNew₁ (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Option (Σ a, β a) :=
  sorry

/--
Inserts the mapping into the map, but does not alter the map if there is already a mapping.
Returns the existing mapping if there is one, or `none` if the given mapping was inserted.
-/
def insertIfNew₂ (m : DHashMap α (fun _ => γ)) (a : α) (b : γ) : DHashMap α (fun _ => γ) × Option γ :=
  sorry

/--
Removes the mapping with the given key if it exists, returning `true` if the map was altered.
-/
def erase' (m : DHashMap α β) (a : α) : DHashMap α β × Bool :=
  sorry

/--
Removes the mapping with the given key if it exists, returning the removed mapping.
-/
def erase₁ (m : DHashMap α β) (a : α) : DHashMap α β × Option (Σ a, β a) :=
  sorry

/--
Removes the mapping with the given key if it exists, returning the removed mapping.
-/
def erase₂ (m : DHashMap α (fun _ => γ)) (a : α) : DHashMap α (fun _ => γ) × Option γ :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are replaced
by their respective last occurrences.
-/
def ofList (l : List (Σ a, β a)) : DHashMap α β :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are replaced
by their respective last occurrences.
-/
def ofList' (l : List (α × γ)) : DHashMap α (fun _ => γ) :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are combined
using the given function.

TODO: Does this need a monadic version?
-/
def ofListWith (l : List (α × γ)) (f : γ → γ → γ) : DHashMap α (fun _ => γ) :=
  sorry

/--
Groups all elements `x`, `y` in `xs` with `key x == key y` into the same array
`(xs.groupByKey key).find! (key x)`. Groups preserve the relative order of elements in `xs`.
-/
def groupByKey (key : γ → α) (xs : Array γ) : DHashMap α (fun _ => Array γ) :=
  sorry

/--
General purpose "modify the mapping for a given key" function that can be used to insert, update
and remove mappings from a hash map.

TODO: this theoretically needs all the variants that insert also has...
TODO: Does this need a monadic version?
-/
def alter (m : DHashMap α (fun _ => γ)) (f : Option γ → Option γ) (k : α) : DHashMap α (fun _ => γ) := sorry

/--
Applies the given mapping function to all entries in the map, discarding entries for which the
mapping function returns `none`.

Does this need a monadic version?
-/
def filterMap (m : DHashMap α β) (f : (a : α) → β a → Option (δ a)) : DHashMap α δ := sorry

/--
Applies the given mapping function to all entries in the map.

TODO: Does this need a monadic version?
-/
def map (m : DHashMap α β) (f : (a : α) → β a → δ a) : DHashMap α δ := sorry

/--
Returns a map that contains only those mappings for which the provided function returns `true`.

TODO: Does this need a monadic version?
-/
def filter (m : DHashMap α β) (f : (a : α) → β a → Bool) : DHashMap α β := sorry

/--
Combines two hash maps using the given combination function.

TODO: Does this need a monadic version?
-/
def mergeWith (m m' : DHashMap α (fun _ => γ)) (f : α → γ → γ → γ) : DHashMap α (fun _ => γ) := sorry

-- Haskell has difference and intersection, but these don't seem very useful to me

/--
Returns a new hash map with the same contents as the input, but with a number of internal buckets that is
reasonable for the number of contained mappings.
-/
def shrinkToFit (m : DHashMap α β) : DHashMap α β := sorry

end modification

section query

/--
If the `BEq` instance is lawful, this function will query the dependent hash map and if a mapping with the given key is
found, the associated value is cast to the required type.
-/
def find?' [LawfulBEq α] (m : DHashMap α β) (a : α) : Option (β a) :=
  sorry

-- We cannot provide a `find?'` version here because `GetElem` is not dependent!
instance : GetElem (DHashMap α β) α (Option (Σ a, β a)) (fun _ _ => True) where
  getElem m k _ := m.findEntry? k

/--
Returns the value associated with the given key, or the given default value if there is no such mapping.

A dependent version of this would be possible, but doesn't sound very useful?
A LawfulBEq dependent version of this would be possible, and is probably useful.
-/
def findD (m : DHashMap α (fun _ => γ)) (a : α) (b₀ : γ) : γ := sorry

/--
Returns the value associated with the given key, or panics if there is no such mapping.

A dependent version of this would be possible, but doesn't sound very useful?
A LawfulBEq dependent version of this would be possible, and is probably useful.
-/
def find! [Inhabited γ] (m : DHashMap α (fun _ => γ)) (a : α) : γ := sorry

/--
Returns the number of mappings contained in the hash map.
-/
def size (m : DHashMap α β) : Nat := sorry

/--
Returns true if there are no mappings contained in the hash map.

Be warned: if your `BEq` instance is not reflexive, or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though is not possible
to get anything out of the hash map.
-/
def isEmpty (m : DHashMap α β) : Bool := sorry

/--
Performs a monadic fold over all mappings contained in the hash map, in some order.
-/
def foldM {m : Type w → Type w} [Monad m] (f : ε → (a : α) → β a → m ε) (init : ε) (h : DHashMap α β) : m ε := sorry

/--
Performs a fold over all mappings contained in the hash map, in some order.
-/
def fold (f : ε → (a : α) → β a → ε) (init : ε) (m : DHashMap α β) : ε := sorry

/--
Perform an action for each mapping contained in the hash map, in some order.
-/
def forM {m : Type w → Type w} [Monad m] (f : (a : α) → β a → m PUnit) (h : DHashMap α β) : m PUnit := sorry

/--
Create a list containing all mappings contained in the hash map, in some order.
-/
def toList (m : DHashMap α β) : List (Σ a, β a) := sorry

/--
Create a list containing all mappings contained in the hash map, in some order.
-/
def toList' (m : DHashMap α (fun _ => γ)) : List (α × γ) := sorry

/--
Create an array containing all mappings contained in the hash map, in some order.
-/
def toArray (m : DHashMap α β) : Array (Σ a, β a) := sorry

/--
Create an array containing all mappings contained in the hash map, in some order.
-/
def toArray' (m : DHashMap α (fun _ => γ)) : Array (α × γ) := sorry

instance [∀ a, BEq (β a)] : BEq (DHashMap α β) := sorry

/--
Create a list containing all keys contained in the hash map, in some order.
-/
def keys (m : DHashMap α β) : List α := sorry

/--
Create a list containing all values contained in the hash map, in some order.
-/
def values (m : DHashMap α (fun _ => γ)) : List γ := sorry

alias assocs := toList

/--
Returns the number of buckets in the internal representation of the hash map.
It should generally not be necessary to call this function other than for things
like monitoring system health.
-/
def numBuckets (m : DHashMap α β) : Nat := sorry

end query

end MyLean.DHashMap.Ops
