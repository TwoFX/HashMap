import Hashmap.List.Associative

inductive MyUnit where
  | pt : MyUnit

instance : BEq MyUnit where
  beq _ _ := false

instance : PartialEquivBEq MyUnit where
  symm := by simp
  trans := by simp

open List

theorem not_findEntry?_ext : ∃ (l l' : List ((_ : MyUnit) × MyUnit)) (_ : l.DistinctKeys) (_ : l'.DistinctKeys)
    (_ : ∀ k, l.findEntry? k = l'.findEntry? k), ¬(l ~ l') := by
  refine ⟨[], [⟨.pt, .pt⟩], by simp, by simp, ?_, ?_⟩
  · rintro ⟨⟩
    rw [findEntry?_nil, findEntry?_cons_of_false, findEntry?_nil]
    rfl
  · simp

theorem not_reflBEq_myUnit [ReflBEq MyUnit] : False := by
  suffices ([] : List ((_ : MyUnit) × MyUnit)) ~ [⟨.pt, .pt⟩] by simp at this
  have : EquivBEq MyUnit := ⟨⟩
  apply findEntry?_ext
  · simp
  · simp
  · intro k
    rfl
