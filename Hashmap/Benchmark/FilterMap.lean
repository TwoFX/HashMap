import Hashmap.DHashMap.Basic

/-!

If you want to run this benchmark, go back to cb4414789b5addafb2418678b118348944a85cdf where all the necessary
functions on the hash map are implemented.

Example run below. This benchmark tests three different implementations of the `filterMap` operation.

* `filterMap₁` filters the buckets using a non-tail-recursive filterMap operation on AssocLists and computes the
  size of the resulting map afterwards
* `filterMap₂` is lifted from Batteries and computes the size of the resulting map while performing the mapping
  using a tail-recursive function `AssocList α β → ULift Nat → AssocList α γ × ULift Nat`.
* `filterMap₃` is like `filterMap₁`, but tail-recursive.

As the sample data below shows, `filterMap₂` is about 40% slower than the other two implementations.
The reason for this is most likely that `filterMap₂` performs an additional `Prod.mk` constructor call
per bucket (recall that hash maps have a lot of buckets). It might be possible to fix this by somehow
convincing the compiler to reuse the memory from the current iteration in the next iteration, but it's
not clear how one would need to change the code to make this work.

-/

open MyLean

def lowercase : List Char :=
  ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
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

def sz : Nat := 2000000

/-- Percentage of mappings that survive the filtering process. The small this number,
    the more pronounced the difference between the implementations is. -/
def resultSize : Nat := 5

---------------------------
-- Option 1: proper hash function
@[noinline] def growInsert (strings : Array String) : IO (DHashMap String (fun _ => Nat)) := do
  let mut m : DHashMap String (fun _ => Nat) := DHashMap.empty sz
  let mut i := 0
  for s in strings do
    m := m.insert s i
    i := i + 1
  return m
---------------------------
-- Option 2: bad hash function (with insert changed to insertUnsafe because otherwise inserting takes way too long)
-- instance : Hashable String where
--   hash _ := 1
-- @[noinline] def growInsert (strings : Array String) : IO (DHashMap String (fun _ => Nat)) := do
--   let mut m : DHashMap String (fun _ => Nat) := DHashMap.empty sz
--   let mut i := 0
--   for s in strings do
--     m := m.insertUnsafe s i
--     i := i + 1
--   return m
---------------------------

@[noinline] def performFilterMap₁ : DHashMap String (fun _ => Nat) → IO Nat :=
  fun m => pure (m.filterMap₁ (fun _ v => if v % 100 < resultSize then some (v + 1) else none)).size

@[noinline] def performFilterMap₂ : DHashMap String (fun _ => Nat) → IO Nat :=
  fun m => pure (m.filterMap₂ (fun _ v => if v % 100 < resultSize then some (v + 1) else none)).size

@[noinline] def performFilterMap₃ : DHashMap String (fun _ => Nat) → IO Nat :=
  fun m => pure (m.filterMap₃ (fun _ v => if v % 100 < resultSize then some (v + 1) else none)).size

@[noinline] def performBenchmark₁ (strings : Array String) : IO Unit := do
  let m ← growInsert strings
  let _ ← timeit "filterMap₁" $ performFilterMap₁ m

@[noinline] def performBenchmark₂ (strings : Array String) : IO Unit := do
  let m ← growInsert strings
  let _ ← timeit "filterMap₂" $ performFilterMap₂ m

@[noinline] def performBenchmark₃ (strings : Array String) : IO Unit := do
  let m ← growInsert strings
  let _ ← timeit "filterMap₃" $ performFilterMap₃ m

def histogram {α : Type u} {β : α → Type v} [BEq α] [Hashable α]
    (m : DHashMap α β) : DHashMap Nat (fun _ => Nat) := Id.run do
  let mut hist : DHashMap Nat (fun _ => Nat) := ∅
  for bucketSize in m.1.buckets.map AssocList.length do
    let newCount : Nat := match hist.findConst? bucketSize with
      | none => 1
      | some n => n + 1
    hist := hist.insert bucketSize newCount
  hist

def main (_ : List String) : IO UInt32 := do
  let strings ← mkMyStrings 8 sz
  let hist := DHashMap.toListModel ((histogram (← growInsert strings)).1.buckets)
  IO.println hist
  for _ in [:20] do
    performBenchmark₁ strings
  for _ in [:20] do
    performBenchmark₂ strings
  for _ in [:20] do
    performBenchmark₃ strings
  return 0


/-!

```
[⟨0, 2603848⟩, ⟨1, 1241048⟩, ⟨2, 296138⟩, ⟨3, 47044⟩, ⟨4, 5639⟩, ⟨5, 537⟩, ⟨6, 47⟩, ⟨7, 3⟩]
filterMap₁ 279ms
filterMap₁ 277ms
filterMap₁ 278ms
filterMap₁ 279ms
filterMap₁ 280ms
filterMap₁ 295ms
filterMap₁ 278ms
filterMap₁ 277ms
filterMap₁ 279ms
filterMap₁ 279ms
filterMap₁ 279ms
filterMap₁ 279ms
filterMap₁ 278ms
filterMap₁ 279ms
filterMap₁ 279ms
filterMap₁ 275ms
filterMap₁ 277ms
filterMap₁ 276ms
filterMap₁ 277ms
filterMap₁ 276ms
filterMap₂ 407ms
filterMap₂ 408ms
filterMap₂ 409ms
filterMap₂ 409ms
filterMap₂ 406ms
filterMap₂ 405ms
filterMap₂ 406ms
filterMap₂ 408ms
filterMap₂ 409ms
filterMap₂ 406ms
filterMap₂ 408ms
filterMap₂ 407ms
filterMap₂ 409ms
filterMap₂ 395ms
filterMap₂ 392ms
filterMap₂ 390ms
filterMap₂ 392ms
filterMap₂ 393ms
filterMap₂ 390ms
filterMap₂ 388ms
filterMap₃ 261ms
filterMap₃ 259ms
filterMap₃ 260ms
filterMap₃ 263ms
filterMap₃ 264ms
filterMap₃ 263ms
filterMap₃ 267ms
filterMap₃ 260ms
filterMap₃ 260ms
filterMap₃ 261ms
filterMap₃ 259ms
filterMap₃ 290ms
filterMap₃ 277ms
filterMap₃ 279ms
filterMap₃ 277ms
filterMap₃ 278ms
filterMap₃ 278ms
filterMap₃ 277ms
filterMap₃ 278ms
filterMap₃ 277ms
```

-/
