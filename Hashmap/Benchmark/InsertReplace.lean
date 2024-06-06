import Hashmap.DHashMap.Basic

/-!
Example run below. This benchmark tests the case of the `insert` operation in case the key is already present.
Turns out this has a linearity bug with rather profound performance implications.

If you want to run this benchmark, go back to 2e04b4f8440dd5900e555d83209cf0c084c18abc where all the necessary
functions on the hash map are implemented.
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

@[noinline] def growInsert (init : DHashMap String (fun _ => Nat)) (strings : Array String) (off : Nat) : (DHashMap String (fun _ => Nat)) := Id.run do
  let mut m : DHashMap String (fun _ => Nat) := init
  let mut i := 0
  for s in strings do
    m := m.insert s (i + off)
    i := i + 1
  return m

@[noinline] def growInsert' (init : DHashMap String (fun _ => Nat)) (a : Array String) (off : Nat) : IO (DHashMap String (fun _ => Nat)) := do
  return growInsert init a off

@[noinline] def growInsertL (init : DHashMap String (fun _ => Nat)) (strings : Array String) (off : Nat) : (DHashMap String (fun _ => Nat)) := Id.run do
  let mut m : DHashMap String (fun _ => Nat) := init
  let mut i := 0
  for s in strings do
    m := m.insertLinear s (i + off)
    i := i + 1
  return m

@[noinline] def growInsert'L (init : DHashMap String (fun _ => Nat)) (a : Array String) (off : Nat) : IO (DHashMap String (fun _ => Nat)) := do
  return growInsertL init a off

def main (_ : List String) : IO UInt32 := do
  let strings ← timeit "mkMyStrings" $ mkMyStrings 8 sz
  for _ in [:20] do
    let init : DHashMap String (fun _ => Nat) := DHashMap.empty sz
    let m ← growInsert' init strings 0
    let _ ← timeit "Nonlinear replace" $ growInsert' m strings 1
  for _ in [:20] do
    let init : DHashMap String (fun _ => Nat) := DHashMap.empty sz
    let m ← growInsert'L init strings 0
    let _ ← timeit "Linear replace" $ growInsert'L m strings 1
  return 0

/-!
mkMyStrings 141ms
Nonlinear replace 915ms
Nonlinear replace 989ms
Nonlinear replace 993ms
Nonlinear replace 988ms
Nonlinear replace 995ms
Nonlinear replace 993ms
Nonlinear replace 985ms
Nonlinear replace 996ms
Nonlinear replace 987ms
Nonlinear replace 984ms
Nonlinear replace 983ms
Nonlinear replace 982ms
Nonlinear replace 984ms
Nonlinear replace 993ms
Nonlinear replace 996ms
Nonlinear replace 988ms
Nonlinear replace 984ms
Nonlinear replace 986ms
Nonlinear replace 984ms
Nonlinear replace 984ms
Linear replace 572ms
Linear replace 571ms
Linear replace 577ms
Linear replace 620ms
Linear replace 579ms
Linear replace 569ms
Linear replace 572ms
Linear replace 572ms
Linear replace 568ms
Linear replace 573ms
Linear replace 575ms
Linear replace 569ms
Linear replace 571ms
Linear replace 618ms
Linear replace 576ms
Linear replace 575ms
Linear replace 566ms
Linear replace 574ms
Linear replace 578ms
Linear replace 578ms

-/
