import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.NormNum

/-!
# The finite arithmetic of the counterexample on primes through 1427

The finite sieve checks trial divisors through 37. All numerical
comparisons use exact integers and rationals.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

abbrev explicitPrimes : Finset ℕ := Nat.primesLE 1427
abbrev explicitOddPrimes : Finset ℕ := explicitPrimes.erase 2

def explicitMarkers : Finset ℕ := {2, 5, 11, 14}

def explicitOddPrimeProduct : ℕ := ∏ p ∈ explicitOddPrimes, p

def explicitUpsilon : ℚ :=
  (1 + 1 / 2 ^ 1) * (1 + 1 / 2 ^ 3) * (1 + 1 / 2 ^ 9) + 1 / 2 ^ 26

def explicitMarkerMass : ℚ := ∑ k ∈ explicitMarkers, 1 / (2 : ℚ) ^ k

def explicitDoubleMarkerMass : ℚ := ∑ k ∈ explicitMarkers, 1 / (2 : ℚ) ^ (2 * k)

def explicitScaledGain : ℚ :=
  explicitMarkerMass - (explicitUpsilon - 1) +
    ∑ q ∈ explicitOddPrimes, (explicitMarkerMass / (q : ℚ) -
      explicitDoubleMarkerMass / (q : ℚ) ^ 2 - (explicitUpsilon - explicitMarkerMass) / (q : ℚ) ^ 3)

private def checkPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 38).all (fun d => decide (d < 2 ∨ n < d * d ∨ ¬ d ∣ n))

private theorem checkPrime_eq_true_iff {n : ℕ} (hn : n ≤ 1427) :
    checkPrime n = true ↔ Nat.Prime n := by
  rw [Nat.prime_def_le_sqrt]
  simp only [checkPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h₂, h⟩
    refine ⟨h₂, fun d hd hd' => ?_⟩
    have hdSq := Nat.le_sqrt.mp hd'
    have hsmall : d < 38 := by
      by_contra! hlarge
      have h := Nat.mul_le_mul hlarge hlarge
      omega
    exact ((h d hsmall).resolve_left hd.not_gt).resolve_left hdSq.not_gt
  · rintro ⟨h₂, h⟩
    refine ⟨h₂, fun d _ => ?_⟩
    by_cases hd : d < 2
    · exact Or.inl hd
    by_cases hd' : n < d * d
    · exact Or.inr (Or.inl hd')
    exact Or.inr (Or.inr (h d (Nat.le_of_not_gt hd) (Nat.le_sqrt.mpr (Nat.le_of_not_gt hd'))))

private def sieve : Finset ℕ :=
  (Finset.range 1428).filter (fun n => checkPrime n = true)

private theorem explicitPrimes_eq_sieve : explicitPrimes = sieve := by
  ext n
  rw [Nat.mem_primesLE, sieve, Finset.mem_filter, Finset.mem_range]
  by_cases hn : n ≤ 1427
  · rw [checkPrime_eq_true_iff hn]
    simp [hn, Nat.lt_succ_iff]
  · simp [hn, Nat.lt_succ_iff]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem explicitPrimes_card : explicitPrimes.card = 225 := by
  rw [explicitPrimes_eq_sieve]
  decide +kernel

theorem explicitOddPrimes_card : explicitOddPrimes.card = 224 := by
  have h₂ : 2 ∈ explicitPrimes := Nat.mem_primesLE.mpr ⟨by decide, Nat.prime_two⟩
  rw [explicitOddPrimes, Finset.card_erase_of_mem h₂, explicitPrimes_card]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem explicitOddPrimeProduct_lt : explicitOddPrimeProduct < 3 * 10 ^ 590 := by
  rw [explicitOddPrimeProduct, explicitOddPrimes, explicitPrimes_eq_sieve]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem explicit_scaledMass_gt : (9 : ℚ) / 100000 < explicitScaledGain := by
  rw [explicitScaledGain, explicitOddPrimes, explicitPrimes_eq_sieve]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem explicit_roughFactor_gt :
    (1 : ℚ) / 15 < (1427 / 1428 : ℚ) * ∏ p ∈ explicitPrimes, (1 - 1 / (p : ℚ)) := by
  rw [explicitPrimes_eq_sieve]
  decide +kernel

end GRHArticle.ProgressionFree
