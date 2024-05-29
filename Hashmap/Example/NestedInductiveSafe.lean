import Hashmap.HashMap.Lemmas

/-!
# Hash map showcase: nested inductive types

In this file, we give an example of a verified algorithm containing a nested inductive type. Since
nested inductive types must satisfy a "positivity condition", we cannot use the normal hash map with
its bundled well-formedness. Instead, we need to put the raw data into the actual inductive, and
declare an inductive predicate for the well-formedness.
-/

open MyLean

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

instance : Hashable Char where
  hash c := hash c.val

inductive RawTrie (α : Type u) where
  | mk : Bool → HashMap.Raw α (RawTrie α) → RawTrie α

namespace RawTrie

def contained : RawTrie α → Bool
  | .mk b _ => b

def children : RawTrie α → HashMap.Raw α (RawTrie α)
  | .mk _ m => m

@[simp] theorem contained_mk {b : Bool} {m : HashMap.Raw α (RawTrie α)} : (RawTrie.mk b m).contained = b := rfl
@[simp] theorem children_mk {b : Bool} {m : HashMap.Raw α (RawTrie α)} : (RawTrie.mk b m).children = m := rfl

def child? [BEq α] [Hashable α] (a : α) (t : RawTrie α) : Option (RawTrie α) :=
  t.children.find? a

def empty : RawTrie α :=
  ⟨false, ∅⟩

@[simp] theorem children_empty : (empty : RawTrie α).children = ∅ := rfl
@[simp] theorem contained_empty : (empty : RawTrie α).contained = false := rfl

@[simp] theorem child?_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (a : α) : (empty : RawTrie α).child? a = none := by
  simp [child?]

instance : EmptyCollection (RawTrie α) where
  emptyCollection := .empty

@[simp] theorem children_emptyc : (∅ : RawTrie α).children = ∅ := rfl
@[simp] theorem contained_emptyc : (∅ : RawTrie α).contained = false := rfl

def child [BEq α] [Hashable α] (a : α) (t : RawTrie α) : RawTrie α :=
  (t.child? a).getD ∅

def contains [BEq α] [Hashable α] : List α → RawTrie α → Bool
  | [], t => t.contained
  | (a::as), t => match t.child? a with
    | none => false
    | some u => u.contains as

@[simp]
theorem contains_nil_mk [BEq α] [Hashable α] {b : Bool} {m : HashMap.Raw α (RawTrie α)} :
    (RawTrie.mk b m).contains [] = b := rfl

def insert [BEq α] [Hashable α] : List α → RawTrie α → RawTrie α
  | [], t => ⟨true, t.children⟩
  | (a::as), t => ⟨t.contained, t.children.insert a ((t.child a).insert as)⟩

inductive WF [BEq α] [Hashable α] : RawTrie α → Prop where
  | mk {t : RawTrie α} : t.children.WF → (∀ c [EquivBEq α] [LawfulHashable α], hasValue t.children c → c.WF) → t.WF

theorem WF.WF_children [BEq α] [Hashable α] {t : RawTrie α} : t.WF → t.children.WF
  | ⟨h, _⟩ => h

theorem WF.WF_of_hasValue [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {t : RawTrie α} : t.WF → ∀ c, hasValue t.children c → c.WF
  | ⟨_, h⟩ => fun c => h c

@[simp]
theorem WF.empty [BEq α] [Hashable α] : (RawTrie.empty : RawTrie α).WF :=
  ⟨by simpa using HashMap.Raw.WF.emptyc, fun _ _ _ => by simp⟩

@[simp]
theorem WF.emptyc [BEq α] [Hashable α] : (∅ : RawTrie α).WF :=
  WF.empty

theorem WF.child? [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {r : RawTrie α} (h : r.WF) {c : α} {s : RawTrie α} (h₂ : r.child? c = some s) :
    s.WF := by
  rcases h with ⟨-, h⟩
  exact h _ ⟨_, h₂⟩

theorem WF.child [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {r : RawTrie α} (h : r.WF) {c : α} : (r.child c).WF := by
  rw [RawTrie.child]
  cases hc : RawTrie.child? c r
  · simp
  · simpa using WF.child? h hc

theorem WF.insert [BEq α] [Hashable α] {l : List α} {t : RawTrie α} (h : t.WF) : (t.insert l).WF := by
  induction l, t using insert.induct
  · rw [RawTrie.insert]
    exact ⟨by simpa using h.WF_children, fun _ _ _ => by simpa using h.WF_of_hasValue _⟩
  · next a as u ih =>
    rw [RawTrie.insert]
    refine ⟨h.WF_children.insert, fun v _ _ hv => ((hasValue_insert h.WF_children).1 hv).elim ?_ ?_⟩
    · exact fun hx => hx ▸ ih h.child
    · rintro ⟨a', -, ha'₂⟩
      exact h.WF_of_hasValue _ ⟨a', ha'₂⟩

@[simp]
theorem contains_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {l : List α} :
    (RawTrie.empty : RawTrie α).contains l = false := by
  induction l <;> simp [contains]

@[simp]
theorem contains_emptyc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {l : List α} :
    (∅ : RawTrie α).contains l = false :=
  contains_empty

example [BEq α] : BEq (List α) := by exact inferInstance

theorem contains_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {l m : List α} {t : RawTrie α} (h : t.WF) :
    (t.insert l).contains m = ((l == m) || t.contains m) := by
  induction l, t using insert.induct generalizing m
  · rw [insert]
    cases m
    · simp only [contains_nil_mk, Bool.cond_true_left, Bool.true_eq, Bool.or_eq_true]
      exact Or.inl rfl
    · next a as =>
      have : ([] == (a :: as)) = false := rfl
      rw [contains, contains, this, Bool.false_or]
      congr
  · next a as u ih =>
    rw [insert]
    cases m
    · have : ((a :: as) == []) = false := rfl
      rw [contains_nil_mk, this, Bool.false_or, contains]
    · next b bs =>
      rw [contains, child?, children_mk, HashMap.Raw.find?_insert _ h.WF_children]
      cases hab : a == b
      · rw [cond_false]
        have : (a :: as == b :: bs) = false := by
          change (a == b && _) = false -- TODO: BEq List lemmas
          rw [hab, Bool.false_and]
        rw [this, Bool.false_or, contains]
        rfl
      · rw [cond_true]
        dsimp only
        rw [ih h.child]
        have : (a :: as == b :: bs) = (as == bs) := by
          change (a == b && _) = (as == bs)
          rw [hab, Bool.true_and]
          rfl
        rw [this]
        congr 1
        rw [contains, child]
        have hch : child? a u = child? b u := by
          rw [child?, child?, HashMap.Raw.find?_congr _ h.WF_children hab]
        rw [hch]
        cases child? b u
        · rw [Option.getD_none, contains_emptyc]
        · rw [Option.getD_some]

end RawTrie

def Trie (α : Type u) [BEq α] [Hashable α] := { r : RawTrie α // r.WF }

namespace Trie

def empty [BEq α] [Hashable α] : Trie α :=
  ⟨RawTrie.empty, RawTrie.WF.empty⟩

instance [BEq α] [Hashable α] : EmptyCollection (Trie α) where
  emptyCollection := .empty

def insert [BEq α] [Hashable α] (l : List α) (t : Trie α) : Trie α :=
  ⟨t.1.insert l, t.2.insert⟩

def contains [BEq α] [Hashable α] (l : List α) (t : Trie α) : Bool :=
  t.1.contains l

@[simp]
theorem contains_empty [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {l : List α} :
    (Trie.empty : Trie α).contains l = false :=
  RawTrie.contains_empty

@[simp]
theorem contains_emptyc [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {l : List α} :
    (∅ : Trie α).contains l = false :=
  RawTrie.contains_emptyc

theorem contains_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {l m : List α} {t : Trie α} :
    (t.insert l).contains m = ((l == m) || t.contains m) :=
  RawTrie.contains_insert t.2

end Trie
