/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

theorem List.bind_eq_foldl (f : α → List β) (l : List α) :
      l.bind f = l.foldl (fun acc a => acc ++ f a) [] := by
  simpa using go []
  where
    go (l') : l' ++ l.bind f = l.foldl (fun acc a => acc ++ f a) l' := by
      induction l generalizing l'
      · simp
      · next h t ih =>
        rw [List.bind_cons, ← List.append_assoc, ih, List.foldl_cons]


section

open Std

variable (f : α → α → α) [Std.Associative f]

theorem foldl_assoc (l : List α) (a₁ a₂ : α) :
    l.foldl f (f a₁ a₂) = f a₁ (l.foldl f a₂) := by
  induction l generalizing a₂
  · simp
  · next h t ih =>
    skip
    rw [List.foldl_cons, List.foldl_cons, ← ih, Associative.assoc (op := f)]

variable (e : α) [Std.LawfulRightIdentity f e]

theorem foldl_ident (l : List α) (a : α) :
    l.foldl f a = f a (l.foldl f e) := by
  rw [← LawfulRightIdentity.right_id (op := f) a, foldl_assoc,
    LawfulRightIdentity.right_id (op := f)]

instance : Std.Associative (List.append (α := α)) := ⟨List.append_assoc⟩
instance : Std.LawfulIdentity (List.append (α := α)) [] where
  left_id := List.nil_append
  right_id := List.append_nil


end
