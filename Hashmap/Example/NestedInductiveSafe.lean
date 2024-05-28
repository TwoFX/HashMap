import Hashmap.HashMap.Lemmas

/-!
# Hash map showcase: nested inductive types

In this file, we give an example of a verified algorithm containing a nested inductive type. Since
nested inductive types must satisfy a "positivity condition", we cannot use the normal hash map with
its bundled well-formedness. Instead, we need to put the raw data into the actual inductive, and
declare an inductive predicate for the well-formedness.
-/

open MyLean

inductive RawTree where
  | leaf : Nat → RawTree
  | internal : HashMap.Raw Nat RawTree → RawTree

def RawTree.child? (n : Nat) : RawTree → Option RawTree
  | .leaf _ => none
  | .internal m => m.find? n

@[simp] theorem RawTree.child?_leaf {n m : Nat} : (RawTree.leaf n).child? m = none := rfl
@[simp] theorem RawTree.child?_internal {m : HashMap.Raw Nat RawTree} {n : Nat} : (RawTree.internal m).child? n = m.find? n := rfl

def hasValue [BEq α] [Hashable α] (m : HashMap.Raw α β) (b : β) : Prop :=
  ∃ a, m.find? a = some b

@[simp]
theorem hasValue_emptyc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (b : β) :
    ¬(hasValue (∅ : HashMap.Raw α β) b) := by
  simp [hasValue]

theorem hasValue_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : HashMap.Raw α β} (h : m.WF) {a : α} {b b' : β} :
    hasValue (m.insert a b) b' ↔ b = b' ∨ ∃ a', (a == a') = false ∧ m.find? a' = some b' := by
  simp only [hasValue, HashMap.Raw.find?_insert _ h, cond_eq_if]
  refine ⟨?_, ?_⟩
  · simp only [forall_exists_index]
    intro a'
    split
    · rintro ⟨rfl⟩
      exact Or.inl rfl
    · exact fun h => Or.inr ⟨a', ⟨by simp_all, h⟩⟩
  · rintro (rfl|⟨a', h₁, h₂⟩)
    · exact ⟨a, by simp⟩
    · exact ⟨a', by simp_all⟩

inductive RawTree.WF : RawTree → Prop where
  | leaf {n} : (RawTree.leaf n).WF
  | internal {m : HashMap.Raw Nat RawTree} :
      m.WF → (∀ t, hasValue m t → t.WF) → (RawTree.internal m).WF

theorem RawTree.WF.child? {r : RawTree} (h : r.WF) {n : Nat} {c : RawTree} (h₂ : r.child? n = some c) :
    c.WF := by
  cases r
  · simp at h₂
  · rcases h with _|⟨-, h⟩
    exact h _ ⟨_, h₂⟩

def Tree := { r : RawTree // r.WF }

def Tree.leaf (n : Nat) : Tree :=
  ⟨.leaf n, .leaf⟩

-- I wonder how hard it would be to convince the compiler to
def Tree.child (n : Nat) (t : Tree) : Option Tree :=
  match h : t.1.child? n with
  | some c => some ⟨c, t.2.child? h⟩
  | none => none

-- set_option trace.compiler.ir.result true in
def Tree.traverse : Tree → List Nat → Option Nat
  | ⟨RawTree.leaf n, _⟩, [] => n
  | t@⟨RawTree.internal _, _⟩, (i :: is) => t.child i |>.bind (·.traverse is)
  | _, _ => none

inductive ListTree where
  | leaf : Nat → ListTree
  | internal : List (Nat × ListTree) → ListTree

def ListTree.toRawTree : ListTree → RawTree
  | .leaf n => .leaf n
  | .internal l => .internal (go ∅ l)
where go (acc : HashMap.Raw Nat RawTree) : List (Nat × ListTree) → HashMap.Raw Nat RawTree
  | [] => acc
  | ⟨n, c⟩::ls => go (acc.insert n c.toRawTree) ls

@[simp]
theorem ListTree.toRawTree_leaf {n : Nat} : (ListTree.leaf n).toRawTree = RawTree.leaf n := by
  rw [ListTree.toRawTree]

theorem ListTree.WF_toRawTree (l : ListTree) : l.toRawTree.WF := by
  suffices (∀ (acc : HashMap.Raw Nat RawTree) (l : List (Nat × ListTree)), acc.WF → (∀ t, hasValue acc t → t.WF) →
    (toRawTree.go acc l).WF ∧ (∀ t, hasValue (toRawTree.go acc l) t → t.WF)) ∧ (∀ l, (ListTree.toRawTree l).WF) from this.2 _
  apply toRawTree.go.mutual_induct
  · intros acc h h'
    refine ⟨?_, ?_⟩ <;> rwa [toRawTree.go]
  · intros acc n c ls hc hins hacc hacc'
    rw [toRawTree.go]
    refine hins hacc.insert fun t h => ((hasValue_insert hacc).1 h).elim (· ▸ hc) ?_
    rintro ⟨a', -, ha'⟩
    exact hacc' _ ⟨a', ha'⟩
  · simpa using fun _ => .leaf
  · intro l h
    rw [ListTree.toRawTree]
    have := h HashMap.Raw.WF.empty (by simp)
    exact .internal this.1 this.2

def ListTree.toTree (t : ListTree) : Tree :=
  ⟨t.toRawTree, WF_toRawTree t⟩
