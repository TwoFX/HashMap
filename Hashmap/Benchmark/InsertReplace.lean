import Hashmap.DHashMap.Basic

/-!
This benchmark tests the case of the `insert` operation in case the key is already present.

Example runs below. There are two variants of this benchmark.

The first variant tested the original implementation which had a linearity bug agains a fixed linear version that
performed `Array.uset i .nil`. The fixed version is about 40% faster.
If you want to run this benchmark, go back to 2e04b4f8440dd5900e555d83209cf0c084c18abc where all the necessary
functions on the hash map are implemented.

The second variant tested the `Array.uset i .nil` version against a version based on `Array.modify`. The difference
between these two versions was less than one standard deviation -> not significant.
If you want to run this benchmark, go back to bfabba0e6b2e19f7da7ce840189d3cbb11bfd586 where all the necessary
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
    m := m.insertModify s (i + off)
    i := i + 1
  return m

@[noinline] def growInsert'L (init : DHashMap String (fun _ => Nat)) (a : Array String) (off : Nat) : IO (DHashMap String (fun _ => Nat)) := do
  return growInsertL init a off

def main (_ : List String) : IO UInt32 := do
  let strings ← timeit "mkMyStrings" $ mkMyStrings 8 sz
  IO.println "Modify"
  for _ in [:20] do
    let init : DHashMap String (fun _ => Nat) := DHashMap.empty sz
    let m ← growInsert'L init strings 0
    let _ ← timeit "" $ growInsert'L m strings 1
  IO.println "Update"
  for _ in [:20] do
    let init : DHashMap String (fun _ => Nat) := DHashMap.empty sz
    let m ← growInsert' init strings 0
    let _ ← timeit "" $ growInsert' m strings 1
  IO.println "Modify"
  for _ in [:20] do
    let init : DHashMap String (fun _ => Nat) := DHashMap.empty sz
    let m ← growInsert'L init strings 0
    let _ ← timeit "" $ growInsert'L m strings 1
  IO.println "Update"
  for _ in [:20] do
    let init : DHashMap String (fun _ => Nat) := DHashMap.empty sz
    let m ← growInsert' init strings 0
    let _ ← timeit "" $ growInsert' m strings 1
  return 0

/-
Variant 1: nonlinear vs linear

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

/-
Variant 2: update vs modify

Aggregated data from two runs (= 80 executions per variant):

        Update	    Modify
Average	569.375	    555.4
Stddev	20.38762034	19.86256577

First run:

mkMyStrings 136ms
Update
 533ms
 574ms
 570ms
 565ms
 579ms
 576ms
 574ms
 572ms
 609ms
 571ms
 571ms
 570ms
 578ms
 575ms
 572ms
 572ms
 612ms
 577ms
 569ms
 569ms
Modify
 562ms
 563ms
 562ms
 560ms
 559ms
 562ms
 560ms
 557ms
 560ms
 564ms
 566ms
 563ms
 591ms
 563ms
 568ms
 587ms
 570ms
 568ms
 568ms
 562ms
Update
 590ms
 578ms
 578ms
 573ms
 576ms
 576ms
 572ms
 607ms
 580ms
 576ms
 577ms
 570ms
 575ms
 571ms
 574ms
 580ms
 574ms
 576ms
 575ms
 632ms
Modify
 568ms
 571ms
 588ms
 564ms
 562ms
 563ms
 560ms
 565ms
 563ms
 564ms
 565ms
 562ms
 562ms
 565ms
 562ms
 585ms
 588ms
 566ms
 569ms
 578ms

Second run:

 mkMyStrings 127ms
Modify
 503ms
 544ms
 557ms
 531ms
 537ms
 526ms
 530ms
 530ms
 538ms
 545ms
 622ms
 565ms
 580ms
 550ms
 530ms
 546ms
 528ms
 526ms
 527ms
 537ms
Update
 552ms
 528ms
 547ms
 540ms
 546ms
 542ms
 540ms
 547ms
 533ms
 551ms
 571ms
 549ms
 537ms
 546ms
 531ms
 533ms
 548ms
 534ms
 547ms
 535ms
Modify
 541ms
 544ms
 527ms
 548ms
 555ms
 527ms
 537ms
 531ms
 542ms
 524ms
 543ms
 527ms
 532ms
 544ms
 528ms
 563ms
 581ms
 569ms
 567ms
 565ms
Update
 577ms
 615ms
 573ms
 571ms
 573ms
 592ms
 592ms
 587ms
 572ms
 608ms
 573ms
 569ms
 570ms
 569ms
 579ms
 580ms
 573ms
 570ms
 573ms
 579ms

-/
