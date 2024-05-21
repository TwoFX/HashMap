/-!
This benchmark tried to test the performance gain of special-casing the default capacity to benefit from
closed subterm lifting. It turns out that it's not necessary to add the special case to the implementation
simply because the entire call with the default value is a closed term, so the two versions are in fact
equivalent w.r.t. the closed subterm optimization. Some things that you can learn from this benchmark:

* as expected, creating a map with the default capacity is significantly faster then with a different capacity
* the compiler is quite smart: it notices that the closed subterms appearing in the two variants are the same
  and only emits one declaration for them
* also, the compiler manages to optimize away the check in `empty₂` in case we use the default argument
* finally, `empty₂` is much faster than `empty₁` if you happen to initialize the map to a capacity that is not known at
  compile time but at runtime turns out to be equal to the default capacity
* `empty₃` is the variant of `empty₂` that you probably would actually want to implement if you elect to go for
  this optimization at all, but it is noticeably slower than `empty₂` because it always needs to do the calls
  to `numBucketsForCapacity` and `nextPowerOfTwo`. Still, much faster than actually allocating the array.
-/

inductive AssocList (α : Type u) (β : α → Type v) where
  | nil
  | cons (key : α) (value : β key) (tail : AssocList α β)

structure Raw (α : Type u) (β : α → Type v) where
  size : Nat
  buckets : Array (AssocList α β)

private def numBucketsForCapacity (capacity : Nat) : Nat :=
  capacity * 4 / 3

@[inline] def empty₁ (α : Type u) (β : α → Type v) (capacity := 8) : Raw α β :=
  ⟨0, mkArray (numBucketsForCapacity capacity).nextPowerOfTwo .nil⟩

@[inline] def empty₂ (α : Type u) (β : α → Type v) (capacity := 8) : Raw α β :=
  if capacity = 8 then
    -- Take advantage of closed subterm lifting
    ⟨0, mkArray (numBucketsForCapacity 8).nextPowerOfTwo .nil⟩
  else
    ⟨0, mkArray (numBucketsForCapacity capacity).nextPowerOfTwo .nil⟩

@[inline] def defaultNumberOfBuckets : Nat :=
  (numBucketsForCapacity 8).nextPowerOfTwo

@[inline] def empty₃ (α : Type u) (β : α → Type v) (capacity := 8) : Raw α β :=
  let numBuckets := (numBucketsForCapacity capacity).nextPowerOfTwo
  if numBuckets = defaultNumberOfBuckets then
    -- Take advantage of closed subterm lifting
    ⟨0, mkArray defaultNumberOfBuckets .nil⟩
  else
    ⟨0, mkArray (numBucketsForCapacity capacity).nextPowerOfTwo .nil⟩

def benchmarkSize := 20000000

@[noinline] def getCapacity : IO Nat := do
  return 8

@[noinline] def doEmpty₁def : IO (Raw Nat (fun _ => Nat)) := do
  return empty₁ _ _

@[noinline] def doEmpty₁cap (capacity : Nat) : IO (Raw Nat (fun _ => Nat)) := do
  return empty₁ _ _ capacity

@[noinline] def benchmark1def : IO PUnit := do
  for _ in [:benchmarkSize] do
    let _ ← doEmpty₁def

@[noinline] def benchmark1cap : IO PUnit := do
  let cap ← getCapacity
  for _ in [:benchmarkSize] do
    let _ ← doEmpty₁cap cap

@[noinline] def doEmpty₂def : IO (Raw Nat (fun _ => Nat)) := do
  return empty₂ _ _

@[noinline] def doEmpty₂cap (capacity : Nat) : IO (Raw Nat (fun _ => Nat)) := do
  return empty₂ _ _ capacity

@[noinline] def benchmark2def : IO PUnit := do
  for _ in [:benchmarkSize] do
    let _ ← doEmpty₂def

@[noinline] def benchmark2cap : IO PUnit := do
  let cap ← getCapacity
  for _ in [:benchmarkSize] do
    let _ ← doEmpty₂cap cap

@[noinline] def doEmpty₃def : IO (Raw Nat (fun _ => Nat)) := do
  return empty₃ _ _

@[noinline] def doEmpty₃cap (capacity : Nat) : IO (Raw Nat (fun _ => Nat)) := do
  return empty₃ _ _ capacity

@[noinline] def benchmark3def : IO PUnit := do
  for _ in [:benchmarkSize] do
    let _ ← doEmpty₃def

@[noinline] def benchmark3cap : IO PUnit := do
  let cap ← getCapacity
  for _ in [:benchmarkSize] do
    let _ ← doEmpty₃cap cap

def main (_ : List String) : IO UInt32 := do
  for _ in [:5] do
    timeit "1def" benchmark1def
  for _ in [:5] do
    timeit "1cap" benchmark1cap
  for _ in [:5] do
    timeit "2def" benchmark2def
  for _ in [:5] do
    timeit "2cap" benchmark2cap
  for _ in [:5] do
    timeit "3def" benchmark3def
  for _ in [:5] do
    timeit "3cap" benchmark3cap
  return 0

/-!
```
1def 127ms
1def 136ms
1def 140ms
1def 139ms
1def 140ms
1cap 598ms
1cap 600ms
1cap 627ms
1cap 611ms
1cap 622ms
2def 137ms
2def 137ms
2def 135ms
2def 137ms
2def 137ms
2cap 155ms
2cap 160ms
2cap 160ms
2cap 163ms
2cap 160ms
3def 137ms
3def 138ms
3def 137ms
3def 137ms
3def 137ms
3cap 275ms
3cap 279ms
3cap 279ms
3cap 279ms
3cap 279ms
```
-/
