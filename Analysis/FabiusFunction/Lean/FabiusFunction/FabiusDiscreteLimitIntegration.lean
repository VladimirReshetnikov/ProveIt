import FabiusFunction.FabiusComplexShiftSpline
import FabiusFunction.FabiusDiscreteLimitToeplitz
import FabiusFunction.FabiusGlobalQBinomialSeries

/-!
# The Fabius discrete-limit formula

This module performs the exact outer q-binomial reindexing, applies the
Toeplitz convergence theorem to the complex-shift spline limit, and connects
the resulting limit with the already proved binary telescope and literal
global q-binomial series.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Finset Filter Set

namespace Fabius

noncomputable section

private theorem two_mul_choose_two_add_discreteLimit (a : ℕ) :
    2 * a.choose 2 + a = a ^ 2 := by
  cases a with
  | zero => simp
  | succ a =>
      rw [two_mul_choose_succ_two]
      ring

private theorem discreteLimit_choose_reindex {n k : ℕ} (hk : k ≤ n) :
    (n - k + 1).choose 2 + (n + k).choose 2 =
      n ^ 2 + 2 * k.choose 2 := by
  have hsub : n - k + k = n := Nat.sub_add_cancel hk
  have hleft := two_mul_choose_succ_two (n - k)
  have hright := two_mul_choose_two_add_discreteLimit (n + k)
  have hkchoose := two_mul_choose_two_add_discreteLimit k
  nlinarith

private theorem discreteLimit_sign_reindex {n k : ℕ} (hk : k ≤ n) :
    (-1 : ℂ) ^ (n - k) * (-1 : ℂ) ^ (n + k) = 1 := by
  rw [← pow_add]
  have hexp : n - k + (n + k) = 2 * n := by omega
  rw [hexp, pow_mul]
  norm_num

private theorem discreteLimit_coefficient_reindex
    {n k : ℕ} (hk : k ≤ n) :
    (1 / ((2 : ℂ) ^ (n ^ 2) * (halfQPochhammer n : ℂ))) *
        ((halfQBinomial n k : ℂ) /
          ((4 : ℂ) ^ k.choose 2 * ((n + k).factorial : ℂ))) =
      discreteLimitWeightIn ℂ n (n - k) *
        ((-1 : ℂ) ^ (n + k) /
          ((2 : ℂ) ^ (n + k).choose 2 *
            ((n + k).factorial : ℂ))) := by
  rw [discreteLimitWeightIn, discreteLimitWeight,
    halfQBinomial_symm hk]
  push_cast
  symm
  have hP : (halfQPochhammer n : ℂ) ≠ 0 := by
    exact_mod_cast halfQPochhammer_ne_zero n
  have hhalf :
      (1 / 2 : ℂ) ^ (n - k + 1).choose 2 =
        1 / (2 : ℂ) ^ (n - k + 1).choose 2 := by
    rw [div_pow]
    norm_num
  have hfour :
      (4 : ℂ) ^ k.choose 2 = (2 : ℂ) ^ (2 * k.choose 2) := by
    rw [show (4 : ℂ) = (2 : ℂ) ^ 2 by norm_num, ← pow_mul]
  have hpow :
      (2 : ℂ) ^ (n - k + 1).choose 2 *
          (2 : ℂ) ^ (n + k).choose 2 =
        (2 : ℂ) ^ (n ^ 2) * (4 : ℂ) ^ k.choose 2 := by
    rw [← pow_add, discreteLimit_choose_reindex hk, pow_add, hfour]
  calc
    ((-1 : ℂ) ^ (n - k) * (halfQBinomial n k : ℂ) *
          (1 / 2 : ℂ) ^ (n - k + 1).choose 2 /
        (halfQPochhammer n : ℂ)) *
        ((-1 : ℂ) ^ (n + k) /
          ((2 : ℂ) ^ (n + k).choose 2 *
            ((n + k).factorial : ℂ))) =
      ((-1 : ℂ) ^ (n - k) * (-1 : ℂ) ^ (n + k)) *
        (halfQBinomial n k : ℂ) /
          ((halfQPochhammer n : ℂ) *
            ((2 : ℂ) ^ (n - k + 1).choose 2 *
              (2 : ℂ) ^ (n + k).choose 2) *
            ((n + k).factorial : ℂ)) := by
      rw [hhalf]
      field_simp [hP]
    _ = (halfQBinomial n k : ℂ) /
          ((halfQPochhammer n : ℂ) *
            ((2 : ℂ) ^ (n ^ 2) * (4 : ℂ) ^ k.choose 2) *
            ((n + k).factorial : ℂ)) := by
      rw [discreteLimit_sign_reindex hk, one_mul, hpow]
    _ = (1 / ((2 : ℂ) ^ (n ^ 2) * (halfQPochhammer n : ℂ))) *
        ((halfQBinomial n k : ℂ) /
          ((4 : ℂ) ^ k.choose 2 * ((n + k).factorial : ℂ))) := by
      field_simp [hP]

/-- Exact finite reindexing of the user's `n`-th expression.  Under
`j = n-k`, every degree is `p = 2n-j`, and the remaining coefficient is the
normalized Toeplitz weight. -/
theorem fabiusDiscreteLimitApproximationComplex_eq_weighted_shiftSpline
    (q : ℂ) (x : ℝ) (n : ℕ) :
    fabiusDiscreteLimitApproximationComplex q x n =
      ∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn ℂ n j *
          fabiusComplexShiftSpline (2 * n - j) q x := by
  rw [fabiusDiscreteLimitApproximationComplex,
    fabiusDiscreteLimitApproximation]
  rw [Finset.mul_sum]
  rw [← Finset.sum_range_reflect
    (fun j => discreteLimitWeightIn ℂ n j *
      fabiusComplexShiftSpline (2 * n - j) q x) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hkRange
  have hk : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hkRange)
  have hidx₁ : n + 1 - 1 - k = n - k := by omega
  rw [hidx₁]
  have hidx₂ : 2 * n - (n - k) = n + k := by omega
  rw [hidx₂, fabiusComplexShiftSpline]
  conv_lhs => rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc]
  rw [discreteLimit_coefficient_reindex hk]
  rfl

/-- The proposed complex discrete limit converges to the signed global
Fabius function for every fixed complex translation. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop (𝓝 (globalFabius x : ℂ)) := by
  have ht :
      Tendsto
        (fun n => ∑ j ∈ Finset.range (n + 1),
          discreteLimitWeightIn ℂ n j *
            fabiusComplexShiftSpline (2 * n - j) q x)
        atTop (𝓝 (globalFabius x : ℂ)) :=
    tendsto_discreteLimitWeightIn_sum
      (K := ℂ)
      (H := fun p => fabiusComplexShiftSpline p q x)
      (L := (globalFabius x : ℂ))
      (fabiusComplexShiftSpline_tendsto_globalFabius q hx)
  apply ht.congr'
  filter_upwards with n
  exact
    (fabiusDiscreteLimitApproximationComplex_eq_weighted_shiftSpline
      q x n).symm

/-- Gaussian-rational translations. -/
theorem fabiusDiscreteLimitApproximationGaussianRat_tendsto_globalFabius
    (a b : ℚ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun n => fabiusDiscreteLimitApproximationGaussianRat a b x n)
      atTop (𝓝 (globalFabius x : ℂ)) := by
  simpa only [fabiusDiscreteLimitApproximationGaussianRat,
    fabiusDiscreteLimitApproximationComplex] using
    fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius
      ((a : ℂ) + (b : ℂ) * Complex.I) hx

private theorem fabiusDiscreteLimitApproximationReal_ofReal
    (q x : ℝ) (n : ℕ) :
    (fabiusDiscreteLimitApproximationReal q x n : ℂ) =
      fabiusDiscreteLimitApproximationComplex (q : ℂ) x n := by
  rw [fabiusDiscreteLimitApproximationReal,
    fabiusDiscreteLimitApproximationComplex,
    fabiusDiscreteLimitApproximation]
  push_cast
  rfl

/-- Arbitrary real translations, with a real-valued limit. -/
theorem fabiusDiscreteLimitApproximationReal_tendsto_globalFabius
    (q : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationReal q x n)
      atTop (𝓝 (globalFabius x)) := by
  have h := fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius
    (q : ℂ) hx
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  apply hre.congr'
  filter_upwards with n
  change (fabiusDiscreteLimitApproximationComplex (q : ℂ) x n).re =
    fabiusDiscreteLimitApproximationReal q x n
  rw [← fabiusDiscreteLimitApproximationReal_ofReal]
  exact Complex.ofReal_re _

/-- Rational translations, stated first in the original real form. -/
theorem fabiusDiscreteLimitApproximationRat_tendsto_globalFabius
    (q : ℚ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationRat q x n)
      atTop (𝓝 (globalFabius x)) := by
  simpa only [fabiusDiscreteLimitApproximationRat,
    fabiusDiscreteLimitApproximationReal] using
      fabiusDiscreteLimitApproximationReal_tendsto_globalFabius (q : ℝ) hx

/-- Fully expanded complex theorem, with the safe range-length version of
the inclusive Wolfram cutoff. -/
theorem fabiusDiscreteLimit_literal_complex_tendsto_globalFabius
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ =>
        (1 /
            ((2 : ℂ) ^ (n ^ 2) *
              (qPochhammer (1 / 2) (1 / 2) n : ℂ))) *
          ∑ k ∈ Finset.range (n + 1),
            ((qBinomial n k (1 / 2) : ℂ) /
                ((4 : ℂ) ^ k.choose 2 * ((n + k).factorial : ℂ))) *
              ∑ r ∈ Finset.range
                  ⌊(2 : ℝ) ^ (n + k) * x + 1 / 2⌋₊,
                (-1 : ℂ) ^ thueMorseBit r *
                  ((r : ℂ) - (2 : ℂ) ^ (n + k) * (x : ℂ) + q) ^
                    (n + k))
      atTop (𝓝 (globalFabius x : ℂ)) := by
  change Tendsto
    (fun n => fabiusDiscreteLimitApproximationComplex q x n)
    atTop (𝓝 (globalFabius x : ℂ))
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius q hx

/-- On `[0,1]`, the same limit is the ordinary bounded Fabius function. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_fabiusReal
    (q : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop (𝓝 (fabiusReal fabius x : ℂ)) := by
  rw [← extendedFabius_eq_fabiusReal fabius fabius_spec hx]
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius q hx.1

/-! ## Link with the binary telescope and its literal global series -/

/-- One binary summand is one step of the residual telescope. -/
theorem globalFabius_binary_telescope_step
    (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (hm : 1 ≤ m) :
    globalBinaryReductionSummand x m =
      binaryReductionRemainder fabius x (m - 1) -
        binaryReductionRemainder fabius x m :=
  globalBinaryReductionSummand_eq_remainder_sub
    fabius fabius_spec x hx m hm

/-- Exact finite telescope through scale `N`, including scale zero. -/
theorem globalFabius_eq_binary_telescope_add_remainder
    (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    globalFabius x =
      (∑ m ∈ Finset.range (N + 1),
        globalBinaryReductionSummand x m) +
      binaryReductionRemainder fabius x N := by
  exact extendedFabius_eq_globalBinaryReductionSum_add_remainder
    fabius fabius_spec x hx N

/-- The finite telescopes converge to the same target as the discrete limit. -/
theorem binary_telescope_tendsto_globalFabius
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.range N,
        globalBinaryReductionSummand x m)
      atTop (𝓝 (globalFabius x)) :=
  tendsto_sum_range_globalBinaryReduction fabius fabius_spec x hx

/-- Limit-to-`tsum` form for the q-independent analytic telescope. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_binary_tsum
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop
      (𝓝 ((↑(∑' m : ℕ, globalBinaryReductionSummand x m) : ℂ))) := by
  rw [← extendedFabius_eq_tsum_globalBinaryReductionSummand
    fabius fabius_spec x hx]
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius q hx

/-- Limit-to-`tsum` form for the fully literal global q-binomial series. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop
      (𝓝 (∑' m : ℕ, qBinomialFabiusGlobalSummand ℂ q x m)) := by
  rw [← globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_complex q x hx]
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius q hx

end

end Fabius
