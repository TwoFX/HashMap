import Std.Data.HashMap

open Std

def growInsert : Unit → Nat := fun _ => Id.run do
  let mut m : HashMap Nat Nat := HashMap.empty
  let mut i := 0
  while i < 10000000 do
    m := m.insert i i
    i := i + 1
  return m.size

def main : List String → IO UInt32
  | _ => do
    let mut k := 0
    let x := growInsert ()
    k := k + x
    IO.println s!"{k}"
    return 0
