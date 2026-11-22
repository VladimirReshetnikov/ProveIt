import Std

/-!
# Bounded witnesses for Bertrand's postulate

All executable definitions use structural recursion on natural numbers.
The propositions expressing their specifications use ordinary Lean naturals.
The module Bertrand closes the large-case premise below. The accompanying
report details how to represent the inductions in the object theory.
-/

namespace Bertrand

/-- Divisor characterization of primality. -/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → ¬ d ∣ p

/-- Check all potential divisors in [2,t] using remainders. -/
def passes (p : Nat) : Nat → Bool
  | 0 => true
  | t+1 => passes p t && (decide (t+1 < 2) || decide (p % (t+1) ≠ 0))

theorem passes_spec (p t : Nat) :
    passes p t = true ↔ ∀ d, 2 ≤ d → d ≤ t → ¬ d ∣ p := by
  induction t with
  | zero =>
    simp [passes]
    omega
  | succ t ih =>
    rw [passes, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨prior, last⟩ d hd hdt hdiv
      by_cases h : d ≤ t
      · exact prior d hd h hdiv
      · have hlast : d = t+1 := by omega
        subst d
        rcases last with h | h
        · omega
        · exact h (Nat.mod_eq_zero_of_dvd hdiv)
    · intro all
      constructor
      · exact fun d hd ht => all d hd (by omega)
      · by_cases h : t+1 < 2
        · exact Or.inl h
        · exact Or.inr (fun hzero => all (t+1) (by omega) (by omega)
              (Nat.dvd_of_mod_eq_zero hzero))

def primeB (p : Nat) : Bool := decide (2 ≤ p) && passes p (p-1)

theorem primeB_spec (p : Nat) : primeB p = true ↔ Prime p := by
  rw [primeB, Bool.and_eq_true, decide_eq_true_eq, passes_spec, Prime]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun d hd hlt => h d hd (by omega)⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun d hd hle => h d hd (by omega)⟩

/-- Scan [lo+1,lo+fuel], keeping the first prime. Zero marks an empty result. -/
def first (lo : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
    let old := first lo k
    if old = 0 then
      if primeB (lo+k+1) then lo+k+1 else 0
    else old

private def Empty (lo fuel : Nat) : Prop :=
  first lo fuel = 0 ∧ ∀ p, lo < p → p ≤ lo+fuel → ¬ Prime p

private def Found (lo fuel : Nat) : Prop :=
  let w := first lo fuel
  lo < w ∧ w ≤ lo+fuel ∧ Prime w ∧ ∀ p, lo < p → p < w → ¬ Prime p

private theorem first_invariant (lo fuel : Nat) : Empty lo fuel ∨ Found lo fuel := by
  induction fuel with
  | zero =>
    left
    exact ⟨rfl, fun p h₁ h₂ => by omega⟩
  | succ k ih =>
    rcases ih with ⟨hz, prior⟩ | ⟨hwlo, whi, hw, hmin⟩
    · by_cases hnew : primeB (lo+k+1) = true
      · right
        simp only [Found, first, hz, if_pos, hnew, Nat.add_succ]
        exact ⟨by omega, by omega, (primeB_spec _).mp hnew, fun p hl hu => prior p hl (by omega)⟩
      · left
        simp only [Empty, first, hz, if_pos, if_neg hnew, Nat.add_succ]
        refine ⟨trivial, ?_⟩
        intro p hl hu hp
        by_cases h : p ≤ lo+k
        · exact prior p hl h hp
        · have eq : p = lo+k+1 := by omega
          exact hnew ((primeB_spec _).mpr (eq ▸ hp))
    · right
      have hnz : first lo k ≠ 0 := by omega
      simp only [Found, first, if_neg hnz, Nat.add_succ]
      exact ⟨hwlo, by omega, hw, hmin⟩

theorem first_of_witness {lo fuel p : Nat} (hlo : lo < p) (hhi : p ≤ lo+fuel) (hp : Prime p) :
    lo < first lo fuel ∧ first lo fuel ≤ p ∧ Prime (first lo fuel) ∧
      ∀ q, lo < q → q < first lo fuel → ¬ Prime q := by
  rcases first_invariant lo fuel with ⟨_, h⟩ | ⟨hl, _, h, hm⟩
  · exact False.elim (h p hlo hhi hp)
  · refine ⟨hl, ?_, h, hm⟩
    by_cases hle : first lo fuel ≤ p
    · exact hle
    · exact False.elim (hm p hlo (by omega) hp)

/-- The same selector implements both endpoint conventions. -/
def witness (n : Nat) : Nat :=
  first n (if 4 ≤ n then n-3 else if n = 1 then 1 else n-1)

def Good (n p : Nat) : Prop := n < p ∧ p < 2*n-2 ∧ Prime p

theorem select_good {n p : Nat} (hn : 4 ≤ n) (h : Good n p) :
    Good n (witness n) ∧ ∀ q, n < q → q < witness n → ¬ Prime q := by
  rcases h with ⟨hl, hu, hp⟩
  have spec := first_of_witness (lo := n) (fuel := n-3) hl (by omega) hp
  simp only [witness, if_pos hn, Good]
  exact ⟨⟨spec.1, by omega, spec.2.2.1⟩, spec.2.2.2⟩

/-- The next prime in a verified chain works for every n up to that prime minus one. -/
private theorem chain_step {a n p : Nat} (ha : a ≤ n) (hn : n < p)
    (hgap : p < 2*a-2) (hp : primeB p = true) : Good n p :=
  ⟨hn, by omega, (primeB_spec p).mp hp⟩

set_option maxRecDepth 8192 in
private theorem small_exists {n : Nat} (hn : 4 ≤ n) (hb : n < 722) :
    ∃ p, Good n p := by
  by_cases h5 : n < 5
  · exact ⟨5, chain_step (a := 4) (by omega) h5 (by decide) (by decide)⟩
  by_cases h7 : n < 7
  · exact ⟨7, chain_step (a := 5) (by omega) h7 (by decide) (by decide)⟩
  by_cases h11 : n < 11
  · exact ⟨11, chain_step (a := 7) (by omega) h11 (by decide) (by decide)⟩
  by_cases h19 : n < 19
  · exact ⟨19, chain_step (a := 11) (by omega) h19 (by decide) (by decide)⟩
  by_cases h31 : n < 31
  · exact ⟨31, chain_step (a := 19) (by omega) h31 (by decide) (by decide)⟩
  by_cases h59 : n < 59
  · exact ⟨59, chain_step (a := 31) (by omega) h59 (by decide) (by decide)⟩
  by_cases h113 : n < 113
  · exact ⟨113, chain_step (a := 59) (by omega) h113 (by decide) (by decide)⟩
  by_cases h223 : n < 223
  · exact ⟨223, chain_step (a := 113) (by omega) h223 (by decide) (by decide)⟩
  by_cases h443 : n < 443
  · exact ⟨443, chain_step (a := 223) (by omega) h443 (by decide) (by decide)⟩
  exact ⟨883, chain_step (a := 443) (by omega) (by omega) (by decide) (by decide)⟩

theorem small {n : Nat} (hn : 4 ≤ n) (hb : n < 722) : Good n (witness n) := by
  obtain ⟨p, hp⟩ := small_exists hn hb
  exact (select_good hn hp).1

/-- Input expected from the binomial and numerical estimates. -/
def NoLargeGap : Prop :=
  ∀ n, 722 ≤ n → (∀ p, n < p → p < 2*n-2 → ¬ Prime p) → False

/-- The only case split needed to turn the large gap contradiction into a
specific witness is the verified disjunction for a bounded scan. -/
theorem strong_of_large (large : NoLargeGap) {n : Nat} (hn : 4 ≤ n) :
    Good n (witness n) := by
  by_cases hb : n < 722
  · exact small hn hb
  · rcases first_invariant n (n-3) with ⟨_, none⟩ | ⟨hl, hu, hp, _⟩
    · exact False.elim (large n (by omega) (fun p hl hu => none p hl (by omega)))
    · simp only [Good, witness, if_pos hn]
      exact ⟨hl, by omega, hp⟩

theorem witness_minimal (large : NoLargeGap) {n q : Nat} (hn : 4 ≤ n)
    (hl : n < q) (hu : q < witness n) : ¬ Prime q :=
  (select_good hn (strong_of_large large hn)).2 q hl hu

theorem weak_of_large (large : NoLargeGap) {n : Nat} (hn : 2 ≤ n) :
    n < witness n ∧ witness n < 2*n ∧ Prime (witness n) := by
  by_cases h4 : 4 ≤ n
  · obtain ⟨hl, hu, hp⟩ := strong_of_large large h4
    exact ⟨hl, by omega, hp⟩
  · have h : n = 2 ∨ n = 3 := by omega
    rcases h with rfl | rfl
    · exact ⟨by decide, by decide, (primeB_spec 3).mp (by decide)⟩
    · exact ⟨by decide, by decide, (primeB_spec 5).mp (by decide)⟩

theorem closed_right_of_large (large : NoLargeGap) {n : Nat} (hn : 1 ≤ n) :
    n < witness n ∧ witness n ≤ 2*n ∧ Prime (witness n) := by
  by_cases h : 2 ≤ n
  · obtain ⟨hl, hu, hp⟩ := weak_of_large large h
    exact ⟨hl, by omega, hp⟩
  · have e : n = 1 := by omega
    subst n
    exact ⟨by decide, by decide, (primeB_spec 2).mp (by decide)⟩

end Bertrand
