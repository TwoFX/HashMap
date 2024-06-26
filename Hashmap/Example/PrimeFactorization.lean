/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Basic

/-!
# Dependent hash map showcase: prime factorization with refinement-style verification and caching

In this file we give an example use case for a dependent hash map in the form of a prime factorization
routine verified using refinement types.

The factorization routine works by repeatedly finding the smallest remaining prime factor using trial divison up to the
square root of the number.

Using a dependent hash map that is made available through the state monad, we are able to provide a cache for the mapping
from a number to its smallest prime factor including the proof that the stored value is in fact the smallest prime factor.
This allows us to speed up the calculation of multiple factorizations by reusing previous results while still being able
to prove that the results are correct.
-/

open Std

def Nat.Prime (n : Nat) : Prop :=
  1 < n ∧ ∀ i j, 1 < i → 1 < j → i * j ≠ n

structure IsSmallestPrimeFactor (n d : Nat) : Prop where
  one_lt : 1 < d
  mod_eq_zero : n % d = 0
  forall_le : ∀ d', 1 < d' → d' < d → n % d' ≠ 0

theorem IsSmallestPrimeFactor.prime {n d : Nat} (h : IsSmallestPrimeFactor n d) : d.Prime := by
  refine ⟨h.one_lt, fun i j hi hj hij => ?_⟩
  have hid : i < d := by rwa [← Nat.mul_one i, ← hij, Nat.mul_lt_mul_left (Nat.lt_trans Nat.zero_lt_one hi)]
  have := h.forall_le i hi
  suffices n % i = 0 by omega
  have := h.mod_eq_zero
  rw [← hij, Nat.mod_mul] at this
  exact Nat.eq_zero_of_add_eq_zero_right this

inductive FindFactorState (n : Nat) (d : Nat) where
  | found : (d' : Nat) → IsSmallestPrimeFactor n d' → FindFactorState n d
  | notFound : (∀ d', 1 < d' → d' ≤ d → n % d' ≠ 0) → FindFactorState n d

theorem Nat.div_dvd {n m : Nat} (h : m ∣ n) : (n / m) ∣ n :=
  ⟨m, (Nat.div_mul_cancel h).symm⟩

-- From mathlib
theorem Nat.div_le_div_left (hcb : c ≤ b) (hc : 0 < c) : a / b ≤ a / c :=
  (Nat.le_div_iff_mul_le hc).2 <| Nat.le_trans (Nat.mul_le_mul_left _ hcb) (Nat.div_mul_le_self _ _)

-- From mathlib
theorem Nat.lt_div_iff_mul_lt (hdn : d ∣ n) (a : Nat) : a < n / d ↔ d * a < n := by
  obtain rfl | hd := d.eq_zero_or_pos
  · simp [Nat.zero_dvd.1 hdn]
  · rw [← Nat.mul_lt_mul_left hd, ← Nat.eq_mul_of_div_eq_right hdn rfl]

-- From mathlib
theorem Nat.div_pos (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
  Nat.pos_of_ne_zero fun h ↦ Nat.lt_irrefl a $
    calc
      a = a % b := by simpa [h] using (mod_add_div a b).symm
      _ < b := mod_lt a hb
      _ ≤ a := hba

abbrev M := StateM (DHashMap Nat fun n => { d : Nat // IsSmallestPrimeFactor n d })

def findFactor (n : Nat) (hn : 1 < n) : M { d : Nat // IsSmallestPrimeFactor n d } := do
  dbg_trace "Requesting {n}"
  let cache ← get
  match cache.get? n with
  | none =>
      let ans := compute n hn
      set (cache.insert n ans)
      return ans
  | some ans => return ans
where
  compute (n : Nat) (hn : 1 < n) : { d : Nat // IsSmallestPrimeFactor n d } :=
    dbg_trace "Cache miss {n}"
    match go n 2 Nat.one_lt_two (by omega) (.notFound (by omega)) with
    | .found d' hd' => ⟨d', hd'⟩
    | .notFound h => ⟨n, ⟨hn, n.mod_self, fun d' h₁ h₂ => have := h _ h₁; by omega⟩⟩
  go (n d : Nat) (hd : 1 < d) (hd₂ : (d - 1) * (d - 1) < n) : FindFactorState n (d - 1) → FindFactorState n (n - 1)
    | .found d' hd' => .found d' hd'
    | .notFound h =>
        -- dbg_trace "Trial dividing {n} % {d}"
        if hx : d = n then
          .notFound (hx ▸ h)
        else if hnd : n % d = 0 then
          .found d ⟨hd, hnd, fun d' h₁ h₂ => have := h _ h₁; by omega⟩
        else
          have hind : ∀ d', 1 < d' → d' ≤ d → n % d' ≠ 0 := fun d' h₁ h₂ => by
            have := h d' h₁
            by_cases h : d = d'
            · exact h ▸ hnd
            · omega
          if hsq : d * d ≥ n then
            .notFound fun d' h₁ h₂ => by
              by_cases hd : d' ≤ d
              · exact hind d' h₁ hd
              · intro hnd'
                have hdvd : (n / d') ∣ n := Nat.div_dvd (Nat.dvd_of_mod_eq_zero hnd')
                rw [Nat.dvd_iff_mod_eq_zero] at hdvd
                have hle : n / d' ≤ d := calc n / d'
                    _ ≤ n / d := Nat.div_le_div_left (by omega) (by omega)
                    _ = (n * d) / (d * d) := (Nat.mul_div_mul_right _ _ (by omega)).symm
                    _ ≤ (n * d) / n := Nat.div_le_div_left hsq (by omega)
                    _ = d := Nat.mul_div_cancel_left _ (by omega)
                suffices 1 < n / d' from hind (n / d') this hle hdvd
                suffices 2 * d' ≤ n by
                  rw [Nat.lt_div_iff_mul_lt (Nat.dvd_of_mod_eq_zero hnd'), Nat.mul_comm]
                  calc 1 * d'
                    _ < 2 * d' := (Nat.mul_lt_mul_right (by omega)).2 Nat.one_lt_two
                    _ ≤ n := this
                obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hnd'
                rw [hk, Nat.mul_comm]
                apply Nat.mul_le_mul_left
                rcases k with k|k
                · omega
                cases k
                · omega
                apply Nat.le_add_left
          else
            have : d < n := calc d
              _ = d * 1 := Nat.mul_one _ |>.symm
              _ < d * d := (Nat.mul_lt_mul_left (by omega)).2 hd
              _ < n := by omega
            go n (d + 1) (by omega) (by simpa using Nat.not_le.1 hsq) (.notFound hind)
  termination_by n - d

def factorize (n : Nat) (hn : 0 < n) : M { l : List Nat // l.foldl (· * ·) 1 = n ∧ ∀ d ∈ l, d.Prime } :=
  go n 1 hn [] rfl (by simp) (Nat.mul_one _)
where
  go (m k : Nat) (hm : 0 < m) (l : List Nat) (hl₁ : l.foldl (· * ·) 1 = k) (hl₂ : ∀ d ∈ l, d.Prime)
      (hmk : m * k = n) : M { l : List Nat // l.foldl (· * ·) 1 = n ∧ ∀ d ∈ l, d.Prime } := do
    if h : m = 1 then
      return ⟨l, by rw [← hmk, h, Nat.one_mul]; exact ⟨hl₁, hl₂⟩⟩
    else
      let ⟨fac, hf⟩ ← findFactor m (by omega)
      have hdvd : fac ∣ m := Nat.dvd_of_mod_eq_zero hf.mod_eq_zero
      have hle : fac ≤ m := Nat.le_of_dvd hm hdvd
      have : m / fac < m := calc m / fac
        _ ≤ m / 2 := Nat.div_le_div_left hf.one_lt Nat.zero_lt_two
        _ < m := by omega
      have hfold : (fac :: l).foldl (· * ·) 1 = k * fac := by
        have : ∀ q (l' : List Nat), l'.foldl (· * ·) q = q * l'.foldl (· * ·) 1 := by
          intro q l'
          induction l' generalizing q
          · simp
          · next h t ih => rw [List.foldl_cons, ih, List.foldl_cons, ih (1 * h), Nat.one_mul, Nat.mul_assoc]
        rw [List.foldl_cons, this, hl₁]
        ac_rfl
      go (m / fac) (k * fac) (Nat.div_pos hle (Nat.lt_trans Nat.zero_lt_one hf.one_lt)) (fac :: l) hfold
        (fun d hd => (List.mem_cons.1 hd).elim (fun h => h ▸ hf.prime) (hl₂ _))
        (by rw [Nat.mul_comm k fac, ← Nat.mul_assoc, Nat.div_mul_cancel hdvd, hmk])

def factorizeAll (start stop : Nat) (h : 0 < start) : Array (List Nat) :=
  go start h #[] |>.run' ∅
where
  go (cur : Nat) (h : 0 < cur) (acc : Array (List Nat)) : M (Array (List Nat)) :=
    if hexc : cur > stop then
      return acc
    else do
      go (cur + 1) (by omega) (acc.push (← (factorize cur h)))
  termination_by stop + 1 - cur

#eval factorizeAll 1000000 1005000 (by decide)
