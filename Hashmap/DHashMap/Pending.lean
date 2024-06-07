/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic

set_option autoImplicit false

universe u v w x

variable {α : Type u} [BEq α] [Hashable α] {β : α → Type v} (γ : Type v) (δ : α → Type w) (ε : Type w)

namespace MyLean.DHashMap.Ops

section modification

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
-/
def insert (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  sorry

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
Returns `true` if there was a previous mapping.
-/
def insertB (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  sorry

def insertGet? [LawfulBEq α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Option (β a) :=
  sorry

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
Returns the previous mapping if there was one.
-/
def insertGetEntry? (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Option (Σ a, β a) :=
  sorry

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
Returns the previous mapping if there was one.
-/
def Const.insertGet? (m : DHashMap α (fun _ => γ)) (a : α) (b : γ) : DHashMap α (fun _ => γ) × Option γ :=
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
def insertIfNewB (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  sorry

/--
Inserts the mapping into the map, but does not alter the map if there is already a mapping.
Returns the existing mapping if there is one, or `none` if the given mapping was inserted.
-/
def insertIfNewGet? (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Option (Σ a, β a) :=
  sorry

/--
Inserts the mapping into the map, but does not alter the map if there is already a mapping.
Returns the existing mapping if there is one, or `none` if the given mapping was inserted.
-/
def Const.insertIfNewGet? (m : DHashMap α (fun _ => γ)) (a : α) (b : γ) : DHashMap α (fun _ => γ) × Option γ :=
  sorry

def Const.computeIfAbsentM [BEq α] [Hashable α] {β : Type u} {m : Type u → Type v} [Monad m]
    (q : DHashMap α (fun _ => β)) (a : α) (f : Unit → m β) : m (DHashMap α (fun _ => β) × β) := sorry

def Const.computeIfAbsent [BEq α] [LawfulBEq α] {β : Type v} (m : DHashMap α (fun _ => β)) (a : α) (f : Unit → β) :
    DHashMap α (fun _ => β) × β := sorry

def computeIfAbsentM [BEq α] [Hashable α] [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
    (q : DHashMap α β) (a : α) (f : Unit → m (β a)) : m (DHashMap α β × β a) := sorry

def computeIfAbsent [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) (f : Unit → β a) :
    DHashMap α β × β a := sorry

/--
General purpose "modify the mapping for a given key" function that can be used to insert, update
and remove mappings from a hash map.
-/
def Const.alterM {γ : Type u} {m : Type u → Type v} [Monad m]
  (q : DHashMap α β) (k : α) (f : Option γ → m (Option γ)) : m (DHashMap α (fun _ => γ)) := sorry

/--
General purpose "modify the mapping for a given key" function that can be used to insert, update
and remove mappings from a hash map.
-/
-- We don't provide variants indicating what changed, mainly because they would be somewhat confusing:
-- would they return the previous mapping, the new mapping, or both? We can always add these later if
-- a use case comes up.
def Const.alter (m : DHashMap α (fun _ => γ)) (f : Option γ → Option γ) (k : α) : DHashMap α (fun _ => γ) := sorry

/--
General purpose "modify the mapping for a given key" function that can be used to insert, update
and remove mappings from a hash map.
-/
def alterM [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
  (q : DHashMap α β) (k : α) (f : Option (β k) → m (Option (β k))) : m (DHashMap α β) := sorry

/--
General purpose "modify the mapping for a given key" function that can be used to insert, update
and remove mappings from a hash map.
-/
def alter [LawfulBEq α] (m : DHashMap α β) (k : α) (f : Option (β k) → Option (β k)) : DHashMap α β := sorry

def remove (m : DHashMap α β) (a : α) : DHashMap α β :=
  sorry

/--
Removes the mapping with the given key if it exists, returning `true` if the map was altered.
-/
def removeB (m : DHashMap α β) (a : α) : DHashMap α β × Bool :=
  sorry

def removeGet? [LawfulBEq α] (m : DHashMap α β) (a : α) : DHashMap α β × Option (β a) :=
  sorry

/--
Removes the mapping with the given key if it exists, returning the removed mapping.
-/
def removeGetEntry? (m : DHashMap α β) (a : α) : DHashMap α β × Option (Σ a, β a) :=
  sorry

/--
Removes the mapping with the given key if it exists, returning the removed mapping.
-/
def Const.removeGet? (m : DHashMap α (fun _ => γ)) (a : α) : DHashMap α (fun _ => γ) × Option γ :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are replaced
by their respective last occurrences.
-/
def ofList (l : List (Σ a, β a)) : DHashMap α β :=
  sorry

def ofArray (l : Array (Σ a, β a)) : DHashMap α β :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are combined
using the given function.
-/
def ofListWithM [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
    (f : (a : α) → β a → β a → m (β a)) (l : List (Σ a, β a)) : m (DHashMap α β) :=
  sorry

def ofArrayWithM [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m]
    (l : Array (Σ a, β a)) (f : (a : α) → β a → β a → m (β a)) : m (DHashMap α β) :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are combined
using the given function.
-/
def ofListWith [LawfulBEq α] (l : List (Σ a, β a)) (f : (a : α) → β a → β a → β a) : DHashMap α β :=
  sorry

def ofArrayWith [LawfulBEq α] (l : Array (Σ a, β a)) (f : (a : α) → β a → β a → β a) : DHashMap α β :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are replaced
by their respective last occurrences.
-/
def Const.ofList (l : List (α × γ)) : DHashMap α (fun _ => γ) :=
  sorry

def Const.ofArray (l : Array (α × γ)) : DHashMap α (fun _ => γ) :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are combined
using the given function.
-/
def Const.ofListWithM {γ : Type u} {m : Type u → Type v} [Monad m] (l : α × γ)
    (f : (a : α) → γ → γ → m γ) : m (DHashMap α (fun _ => γ)) :=
  sorry

def Const.ofArrayWithM {γ : Type u} {m : Type u → Type v} [Monad m] (l : α × γ)
    (f : (a : α) → γ → γ → m γ) : m (DHashMap α (fun _ => γ)) :=
  sorry

/--
Builds a `HashMap` from a list of key-value pairs. Values of duplicated keys are combined
using the given function.
-/
def Const.ofListWith (l : List (α × γ)) (f : γ → γ → γ) : DHashMap α (fun _ => γ) :=
  sorry

def Const.ofArrayWith (l : List (α × γ)) (f : γ → γ → γ) : DHashMap α (fun _ => γ) :=
  sorry

/--
Groups all elements `x`, `y` in `xs` with `key x == key y` into the same array
`(xs.groupByKey key).find! (key x)`. Groups preserve the relative order of elements in `xs`.

We won't actually provide a version of this returning a `DHashMap`, only a `HashMap`.
-/
def _root_.Array.groupByKey' (key : γ → α) (xs : Array γ) : DHashMap α (fun _ => Array γ) :=
  sorry

def _root_.List.groupByKey' (key : γ → α) (xs : List γ) : DHashMap α (fun _ => Array γ) :=
  sorry

/--
Applies the given mapping function to all entries in the map, discarding entries for which the
mapping function returns `none`.
-/
def filterMapM {β : α → Type u} {δ : α → Type u} {m : Type u → Type v} [Monad m] (q : DHashMap α β)
    (f : (a : α) → β a → m (Option (δ a))) : m (DHashMap α δ) := sorry

/--
Applies the given mapping function to all entries in the map, discarding entries for which the
mapping function returns `none`.
-/
def filterMap (m : DHashMap α β) (f : (a : α) → β a → Option (δ a)) : DHashMap α δ := sorry

/--
Applies the given mapping function to all entries in the map.
-/
def mapM {β : α → Type u} {δ : α → Type u} {m : Type u → Type v} [Monad m] (q : DHashMap α β)
    (f : (a : α) → β a → m (δ a)) : m (DHashMap α δ) := sorry

/--
Applies the given mapping function to all entries in the map.
-/
def map (m : DHashMap α β) (f : (a : α) → β a → δ a) : DHashMap α δ := sorry

/--
Returns a map that contains only those mappings for which the provided function returns `true`.
-/
def filterM {α : Type} [BEq α] [Hashable α] {β : α → Type} {m : Type → Type u} [Monad m]
    (q : DHashMap α β) (f : (a : α) → β a → m Bool) : m (DHashMap α β) := sorry

/--
Returns a map that contains only those mappings for which the provided function returns `true`.
-/
def filter (m : DHashMap α β) (f : (a : α) → β a → Bool) : DHashMap α β := sorry

/--
Combines two hash maps using the given combination function.
-/
def mergeWithM [LawfulBEq α] {β : α → Type u} {m : Type u → Type v} [Monad m] (q q' : DHashMap α β)
    (f : (a : α) → β a → β a → m (β a)) : m (DHashMap α β) := sorry

/--
Combines two hash maps using the given combination function.
-/
def mergeWith [LawfulBEq α] (m m' : DHashMap α β) (f : (a : α) → β a → β a → β a) : DHashMap α β := sorry

/--
Combines two hash maps using the given combination function.
-/
def Const.mergeWithM {γ : Type u} {m : Type u → Type v} [Monad m] (q q' : DHashMap α (fun _ => γ))
    (f : (a : α) → γ → γ → m γ) : m (DHashMap α (fun _ => γ)) := sorry

/--
Combines two hash maps using the given combination function.
-/
def Const.mergeWith (m m' : DHashMap α (fun _ => γ)) (f : α → γ → γ → γ) : DHashMap α (fun _ => γ) := sorry

/--
Returns a new hash map with the same contents as the input, but with a number of internal buckets that is
reasonable for the number of contained mappings.
-/
def shrinkToFit (m : DHashMap α β) : DHashMap α β := sorry

end modification

section query

instance : Membership α (DHashMap α β) where
  mem a m := m.contains a

def getEntry (m : DHashMap α β) (a : α) (_ : a ∈ m) : Σ a, β a := sorry

def getEntry? (m : DHashMap α β) (a : α) : Option (Σ a, β a) := sorry

def getEntry! [Inhabited (Σ a, β a)] (m : DHashMap α β) (a : α) : Σ a, β a := sorry

def getEntryD (m : DHashMap α β) (a : α) (default : Σ a, β a) : Σ a, β a := sorry

def get [LawfulBEq α] (m : DHashMap α β) (a : α) (_ : a ∈ m) : β a := sorry

/--
If the `BEq` instance is lawful, this function will query the dependent hash map and if a mapping with the given key is
found, the associated value is cast to the required type.
-/
def get? [LawfulBEq α] (m : DHashMap α β) (a : α) : Option (β a) :=
  sorry

def get! [LawfulBEq α] (m : DHashMap α β) (a : α) [Inhabited (β a)] : β a :=
  sorry

def getD [LawfulBEq α] (m : DHashMap α β) (a : α) (default : β a) : β a :=
  sorry

def getWithCast (m : DHashMap α β) (a : α) (_ : a ∈ m) (cast : ∀ {b}, b == a → β b → β a) : β a := sorry
def getWithCast? (m : DHashMap α β) (a : α) (cast : ∀ {b}, b == a → β b → β a) : Option (β a) := sorry
def getWithCast! (m : DHashMap α β) (a : α) [Inhabited (β a)] (cast : ∀ {b}, b == a → β b → β a) : β a := sorry
def getWithCastD (m : DHashMap α β) (a : α) (default : β a) (cast : ∀ {b}, b == a → β b → β a) : β a := sorry

def contains (m : DHashMap α β) (a : α) : Bool := sorry

def getKey (m : DHashMap α β) (a : α) (_ : a ∈ m) : α := sorry

-- This will become `get` in `HashSet`.
def getKey? (m : DHashMap α β) (a : α) : Option α := sorry

-- TODO: should this just build an inhabited instance using `a` or are we afraid of instance clashes here?
def getKey! (m : DHashMap α β) (a : α) [Inhabited α] : α := sorry

def getKeyD (m : DHashMap α β) (a : α) (default : α) : α := sorry

-- We cannot provide a `find?'` version here because `GetElem` is not dependent!
instance : GetElem (DHashMap α β) α (Option (Σ a, β a)) (fun _ _ => True) where
  getElem m k _ := m.findEntry? k

def Const.get (m : DHashMap α (fun _ => γ)) (a : α) (_ : a ∈ m) : γ := sorry

def Const.get? (m : DHashMap α (fun _ => γ)) (a : α) : Option γ := sorry

/--
Returns the value associated with the given key, or the given default value if there is no such mapping.
-/
def Const.getD (m : DHashMap α (fun _ => γ)) (a : α) (b₀ : γ) : γ := sorry

/--
Returns the value associated with the given key, or panics if there is no such mapping.
-/
def Const.get! [Inhabited γ] (m : DHashMap α (fun _ => γ)) (a : α) : γ := sorry

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
def Const.toList (m : DHashMap α (fun _ => γ)) : List (α × γ) := sorry

/--
Create an array containing all mappings contained in the hash map, in some order.
-/
def toArray (m : DHashMap α β) : Array (Σ a, β a) := sorry

/--
Create an array containing all mappings contained in the hash map, in some order.
-/
def Const.toArray (m : DHashMap α (fun _ => γ)) : Array (α × γ) := sorry

instance [LawfulBEq α] [∀ a, BEq (β a)] : BEq (DHashMap α β) := sorry

/--
Create a list containing all keys contained in the hash map, in some order.
-/
def keys (m : DHashMap α β) : List α := sorry

/--
Create a list containing all values contained in the hash map, in some order.
-/
def Const.values (m : DHashMap α (fun _ => γ)) : List γ := sorry

alias assocs := toList

/--
Returns the number of buckets in the internal representation of the hash map.
It should generally not be necessary to call this function other than for things
like monitoring system health.
-/
def Internal.numBuckets (m : DHashMap α β) : Nat := sorry

end query

end MyLean.DHashMap.Ops
