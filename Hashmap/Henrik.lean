import Hashmap.DHashMap.Lemmas

open MyLean

set_option autoImplicit false

universe u

variable {α : Type u} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]


inductive Inv1 : Nat → DHashMap α (fun _ => Nat) → Prop where
| empty : Inv1 0 (DHashMap.empty)
| insert {n : Nat} {map : DHashMap α (fun _ => Nat)} {x : α}
    (hinv : Inv1 n map) (hfind : map.findEntry? x = none) : Inv1 (n + 1) (map.insert x n)

axiom Inv1.property {n m : Nat} (x y : α) (map : DHashMap α (fun _ => Nat)) (hinv : Inv1 n map)
    (hfound1 : map.find? x = some m) (hfound2 : map.find? y = some m) : x = y
