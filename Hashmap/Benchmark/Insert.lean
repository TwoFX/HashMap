import Batteries.Data.HashMap
import Hashmap.DHashMap.Basic

/-!
Example run below. This benchmark tests the `insert` operation of the present hash map, the Lean hash map
and the Batteries hash map.

Takeaways:
* The Batteries hash map is about 10% slower, due to https://github.com/leanprover/lean4/issues/4191
* Implementing `mkIdx` in C++ doesn't seem to make a difference, which isn't too surprising since all
  of the operations happen on USize, which should be fast when compiled from Lean. The two versions
  probably only differ slightly in their initial boxing/unboxing, but I didn't check this in detail.

-/

open MyLean

def lowercase : List Char :=
  [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
    'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']

partial def mkStrings (len num : Nat) : Array String := Id.run do
  if len = 0 then
    return #[""]

  let inner := mkStrings (len - 1) ((num + 25) / 26)
  let mut hv : Nat := 0
  let mut ans : Array String := #[]
  for i in inner do
    for c in lowercase do
      ans := ans.push (i.push c)
      hv := hv + 1
      if hv = num then
        break
    if hv = num then
      break
  ans

@[noinline] def mkMyStrings (num len : Nat) : IO (Array String) := do
  return mkStrings num len

def sz : Nat := 3000000
def presize : Bool := false

@[noinline] def growInsert' (strings : Array String) : (DHashMap String (fun _ => Nat)) := Id.run do
  let mut m : DHashMap String (fun _ => Nat) := bif presize then DHashMap.empty sz else DHashMap.empty
  let mut i := 0
  for s in strings do
    m := m.insert s i
    i := i + 1
  return m

@[noinline] def growInsert'' (a : Array String) : IO (DHashMap String (fun _ => Nat)) := do
  return growInsert' a

@[noinline] def growInsertL (strings : Array String) : (Lean.HashMap String Nat) := Id.run do
  let mut m : Lean.HashMap String Nat := bif presize then Lean.mkHashMap sz else Lean.mkHashMap
  let mut i := 0
  for s in strings do
    m := m.insert s i
    i := i + 1
  return m

@[noinline] def growInsertL' (strings : Array String) : IO (Lean.HashMap String Nat) := do
  return growInsertL strings

@[noinline] def growInsertB (strings : Array String) : (Batteries.HashMap String Nat) := Id.run do
  let mut m : Batteries.HashMap String Nat := bif presize then Batteries.mkHashMap sz else Batteries.mkHashMap
  let mut i := 0
  for s in strings do
    m := m.insert s i
    i := i + 1
  return m

@[noinline] def growInsertB' (strings : Array String) : IO (Batteries.HashMap String Nat) := do
  return growInsertB strings

def main (_ : List String) : IO UInt32 := do
  let strings ← timeit "mkMyStrings" $ mkMyStrings 8 sz
  for _ in [:20] do
    let _ ← timeit "This hash map" $ growInsert'' strings
  for _ in [:20] do
    let _ ← timeit "Lean hash map" $ growInsertL' strings
  for _ in [:20] do
    let _ ← timeit "Bats hash map" $ growInsertB' strings
  return 0

/-!
```
mkMyStrings 136ms
This hash map 918ms
This hash map 895ms
This hash map 947ms
This hash map 859ms
This hash map 934ms
This hash map 889ms
This hash map 896ms
This hash map 890ms
This hash map 896ms
This hash map 893ms
This hash map 892ms
This hash map 894ms
This hash map 899ms
This hash map 898ms
This hash map 894ms
This hash map 951ms
This hash map 902ms
This hash map 897ms
This hash map 897ms
This hash map 899ms
Lean hash map 895ms
Lean hash map 886ms
Lean hash map 895ms
Lean hash map 885ms
Lean hash map 915ms
Lean hash map 896ms
Lean hash map 896ms
Lean hash map 902ms
Lean hash map 899ms
Lean hash map 889ms
Lean hash map 896ms
Lean hash map 897ms
Lean hash map 888ms
Lean hash map 894ms
Lean hash map 897ms
Lean hash map 893ms
Lean hash map 905ms
Lean hash map 899ms
Lean hash map 897ms
Lean hash map 896ms
Bats hash map 1.03s
Bats hash map 1.04s
Bats hash map 1.03s
Bats hash map 1.03s
Bats hash map 1.04s
Bats hash map 1.04s
Bats hash map 1.03s
Bats hash map 1.04s
Bats hash map 1.03s
Bats hash map 1.03s
Bats hash map 1.03s
Bats hash map 1.03s
Bats hash map 1.03s
Bats hash map 1.03s
Bats hash map 1.04s
Bats hash map 1.03s
Bats hash map 1.02s
Bats hash map 1.02s
Bats hash map 1.03s
Bats hash map 1.03s
```

-/
