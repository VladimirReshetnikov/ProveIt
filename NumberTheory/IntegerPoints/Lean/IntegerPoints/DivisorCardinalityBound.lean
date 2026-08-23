import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# A subpolynomial bound for the divisor function

This file proves the elementary estimate

`#n.divisors ≤ Cₑ n^ε` for every `ε > 0` and every `n ≥ 1`,

with an explicit (deliberately crude) constant.  The proof uses only unique
factorisation and Bernoulli's inequality.  Put

`K = ⌈ 2^(1 / ε) ⌉`.

For a prime power `p^a` with `p ≥ K`, we have

`a + 1 ≤ 2^a ≤ p^(ε a)`.

There are only finitely many primes below `K`.  For any integer `p ≥ 2`,
Bernoulli's inequality, applied to `r = p^ε > 1`, gives

`a + 1 ≤ (r / (r - 1)) r^a`.

Multiplying these local inequalities over the prime factorisation of `n`
proves the result.  To keep the constant and its proof simple, its finite
product includes every integer in `[2, K)`, not just the primes.
-/

open scoped BigOperators

namespace LeanProofs.IntegerPoints

namespace DivisorCardinality

noncomputable section

/-- The point beyond which `2 ≤ p^ε`. -/
def primeThreshold (ε : ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ ε⁻¹⌉₊

/-- The fixed cost used to absorb the exponent of a small prime. -/
def smallPrimeRatio (ε : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ ε / ((p : ℝ) ^ ε - 1)

/-- A prime below `primeThreshold ε` pays `smallPrimeRatio ε p`; a larger
prime pays no fixed cost. -/
def primeCost (ε : ℝ) (p : ℕ) : ℝ :=
  if p < primeThreshold ε then smallPrimeRatio ε p else 1

/-- An explicit constant for the divisor bound.  Including composites in the
product makes the finite-set comparison independent of a primality filter. -/
def divisorBoundConstant (ε : ℝ) : ℝ :=
  ∏ p ∈ Finset.Ico 2 (primeThreshold ε), smallPrimeRatio ε p

theorem two_le_primeThreshold_rpow {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) ≤ (primeThreshold ε : ℝ) ^ ε := by
  have hceil : (2 : ℝ) ^ ε⁻¹ ≤ (primeThreshold ε : ℝ) := by
    exact Nat.le_ceil _
  calc
    (2 : ℝ) = ((2 : ℝ) ^ ε⁻¹) ^ ε :=
      (Real.rpow_inv_rpow (by norm_num) hε.ne').symm
    _ ≤ (primeThreshold ε : ℝ) ^ ε :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hceil hε.le

theorem one_le_smallPrimeRatio {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : 2 ≤ p) :
    1 ≤ smallPrimeRatio ε p := by
  have hp1Nat : 1 < p := lt_of_lt_of_le Nat.one_lt_two hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1Nat
  have hr : (1 : ℝ) < (p : ℝ) ^ ε := Real.one_lt_rpow hp1 hε
  rw [smallPrimeRatio]
  exact (le_div_iff₀ (sub_pos.mpr hr)).2 (by linarith)

/-- Bernoulli's inequality in the elementary form `a + 1 ≤ 2^a`. -/
private theorem cast_succ_le_two_pow (a : ℕ) :
    ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := by
  have h := one_add_mul_sub_le_pow (a := (2 : ℝ)) (by norm_num) a
  norm_num at h ⊢
  linarith

/-- A small prime's exponent is absorbed by its fixed geometric cost. -/
private theorem cast_succ_le_smallPrimeRatio_mul_pow
    {ε : ℝ} (hε : 0 < ε) {p a : ℕ} (hp : 2 ≤ p) :
    ((a + 1 : ℕ) : ℝ) ≤ smallPrimeRatio ε p * (((p : ℝ) ^ ε) ^ a) := by
  let r : ℝ := (p : ℝ) ^ ε
  have hp1Nat : 1 < p := lt_of_lt_of_le Nat.one_lt_two hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1Nat
  have hr : 1 < r := by
    simpa only [r] using Real.one_lt_rpow hp1 hε
  have hrSub : 0 < r - 1 := sub_pos.mpr hr
  have hBernoulli : 1 + (a : ℝ) * (r - 1) ≤ r ^ a :=
    one_add_mul_sub_le_pow (by linarith) a
  have haMul : (a : ℝ) * (r - 1) ≤ r ^ a := by
    linarith
  have ha : (a : ℝ) ≤ r ^ a / (r - 1) :=
    (le_div_iff₀ hrSub).2 haMul
  have hone : (1 : ℝ) ≤ r ^ a := one_le_pow₀ hr.le
  rw [smallPrimeRatio]
  change ((a + 1 : ℕ) : ℝ) ≤ r / (r - 1) * r ^ a
  calc
    ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by norm_num
    _ ≤ r ^ a / (r - 1) + r ^ a := add_le_add ha hone
    _ = r / (r - 1) * r ^ a := by
      field_simp [ne_of_gt hrSub]
      ring

/-- The local estimate for one prime in the factorisation of `n`. -/
private theorem factorization_succ_le_cost_mul_pow
    {ε : ℝ} (hε : 0 < ε) {n p : ℕ} (hp : p ∈ n.primeFactors) :
    ((n.factorization p + 1 : ℕ) : ℝ) ≤
      primeCost ε p * (((p : ℝ) ^ ε) ^ n.factorization p) := by
  rw [primeCost]
  split_ifs with hpSmall
  · exact cast_succ_le_smallPrimeRatio_mul_pow hε
      (Nat.prime_of_mem_primeFactors hp).two_le
  · simp only [one_mul]
    have hThreshold : primeThreshold ε ≤ p := Nat.le_of_not_gt hpSmall
    have hThresholdCast : (primeThreshold ε : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hThreshold
    have hBase : (2 : ℝ) ≤ (p : ℝ) ^ ε :=
      (two_le_primeThreshold_rpow hε).trans
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hThresholdCast hε.le)
    exact (cast_succ_le_two_pow (n.factorization p)).trans
      (pow_le_pow_left₀ (by norm_num) hBase _)

/-- All fixed prime costs are bounded by the finite product defining
`divisorBoundConstant`. -/
private theorem primeCost_product_le_constant
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∏ p ∈ n.primeFactors, primeCost ε p) ≤ divisorBoundConstant ε := by
  have hfilter :
      (∏ p ∈ n.primeFactors, primeCost ε p) =
        ∏ p ∈ n.primeFactors.filter (fun p ↦ p < primeThreshold ε),
          smallPrimeRatio ε p := by
    simpa only [primeCost] using
      (Finset.prod_filter (s := n.primeFactors)
        (fun p ↦ p < primeThreshold ε) (smallPrimeRatio ε)).symm
  rw [hfilter, divisorBoundConstant]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hpFactors, hpSmall⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Ico.mpr
      ⟨(Nat.prime_of_mem_primeFactors hpFactors).two_le, hpSmall⟩
  · intro p hp
    exact zero_le_one.trans <|
      one_le_smallPrimeRatio hε
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
  · intro p hp _
    exact one_le_smallPrimeRatio hε (Finset.mem_Ico.mp hp).1

theorem one_le_divisorBoundConstant {ε : ℝ} (hε : 0 < ε) :
    1 ≤ divisorBoundConstant ε := by
  rw [divisorBoundConstant]
  apply Finset.one_le_prod
  intro p hp
  exact one_le_smallPrimeRatio hε (Finset.mem_Ico.mp hp).1

/-- The product of the `p^(ε a)` terms is exactly `n^ε`. -/
private theorem primeFactor_rpow_product
    {ε : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) = (n : ℝ) ^ ε := by
  have hnProduct :
      (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.prod_primeFactors_pow_factorization hn)
  calc
    (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
        ∏ p ∈ n.primeFactors, (((p : ℝ) ^ n.factorization p) ^ ε) := by
      apply Finset.prod_congr rfl
      intro p _
      calc
        ((p : ℝ) ^ ε) ^ n.factorization p =
            (p : ℝ) ^ (ε * (n.factorization p : ℝ)) :=
          (Real.rpow_mul_natCast (Nat.cast_nonneg p) ε (n.factorization p)).symm
        _ = (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by rw [mul_comm]
        _ = ((p : ℝ) ^ n.factorization p) ^ ε :=
          Real.rpow_natCast_mul (Nat.cast_nonneg p) (n.factorization p) ε
    _ = (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p)) ^ ε :=
      Real.finsetProd_rpow n.primeFactors
        (fun p ↦ (p : ℝ) ^ n.factorization p) (fun _ _ ↦ by positivity) ε
    _ = (n : ℝ) ^ ε := by rw [← hnProduct]

/-- The explicit pointwise divisor bound. -/
theorem card_divisors_le_divisorBoundConstant
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    ((n.divisors.card : ℕ) : ℝ) ≤ divisorBoundConstant ε * (n : ℝ) ^ ε := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  calc
    ((n.divisors.card : ℕ) : ℝ) =
        ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
      rw [Nat.card_divisors hn0, Nat.cast_prod]
    _ ≤ ∏ p ∈ n.primeFactors,
        primeCost ε p * (((p : ℝ) ^ ε) ^ n.factorization p) :=
      Finset.prod_le_prod (fun _ _ ↦ by positivity)
        (fun p hp ↦ factorization_succ_le_cost_mul_pow hε hp)
    _ = (∏ p ∈ n.primeFactors, primeCost ε p) *
        ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_mul_distrib
    _ ≤ divisorBoundConstant ε *
        ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p :=
      mul_le_mul_of_nonneg_right (primeCost_product_le_constant hε n) (by positivity)
    _ = divisorBoundConstant ε * (n : ℝ) ^ ε := by
      rw [primeFactor_rpow_product hn0]

/-- A version of the subpolynomial bound which also records that the chosen
constant is at least one. -/
theorem exists_one_le_card_divisors_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ ε := by
  refine ⟨divisorBoundConstant ε, one_le_divisorBoundConstant hε, ?_⟩
  intro n hn
  exact card_divisors_le_divisorBoundConstant hε hn

/-- The classical subpolynomial divisor bound, in the usual quantified form. -/
theorem exists_card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, _, hC⟩ := exists_one_le_card_divisors_bound ε hε
  exact ⟨C, hC⟩

end

end DivisorCardinality

end LeanProofs.IntegerPoints
