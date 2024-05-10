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

end query

end MyLean.DHashMap.Ops
