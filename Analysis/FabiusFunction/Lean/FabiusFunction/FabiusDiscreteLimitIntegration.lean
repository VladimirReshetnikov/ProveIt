import FabiusFunction.FabiusComplexShiftSpline
import FabiusFunction.FabiusDiscreteLimitToeplitz
import FabiusFunction.FabiusGlobalQBinomialSeries

/-!
# The Fabius discrete-limit formula

This module performs the exact outer q-binomial reindexing, applies the
Toeplitz convergence theorem to the complex-shift spline limit, and connects
the resulting limit with the already proved binary telescope and literal
global q-binomial series.  Exact empty-prefix vanishing extends the main
convergence theorem from the nonnegative axis to every real input.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Finset Filter Set

namespace Fabius

noncomputable section

private theorem discreteLimit_choose_reindex {n k : ℕ} (hk : k ≤ n) :
    (n - k + 1).choose 2 + (n + k).choose 2 =
      n ^ 2 + 2 * k.choose 2 := by
  have hsub : n - k + k = n := Nat.sub_add_cancel hk
  have hleft := two_mul_choose_succ_two (n - k)
  have hright := two_mul_choose_two_add (n + k)
  have hkchoose := two_mul_choose_two_add k
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

/-- Complex-shift discrete-limit approximants converge on the whole real
line.  On the nonpositive half-line both sides vanish exactly. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all
    (q : ℂ) (x : ℝ) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop (𝓝 (globalFabius x : ℂ)) := by
  rcases le_total 0 x with hx | hx
  · exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius q hx
  · have happ (n : ℕ) :
        fabiusDiscreteLimitApproximationComplex q x n = 0 :=
      fabiusDiscreteLimitApproximationComplex_eq_zero_of_nonpos q hx n
    have hglobal : globalFabius x = 0 := by
      change extendedFabius fabius x = 0
      exact extendedFabius_eq_zero_of_nonpos fabius fabius_spec hx
    simp [happ, hglobal]

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

/-- Gaussian-rational translations converge on the whole real line. -/
theorem fabiusDiscreteLimitApproximationGaussianRat_tendsto_globalFabius_all
    (a b : ℚ) (x : ℝ) :
    Tendsto
      (fun n => fabiusDiscreteLimitApproximationGaussianRat a b x n)
      atTop (𝓝 (globalFabius x : ℂ)) := by
  simpa only [fabiusDiscreteLimitApproximationGaussianRat,
    fabiusDiscreteLimitApproximationComplex] using
    fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all
      ((a : ℂ) + (b : ℂ) * Complex.I) x

/-- Casting the real-shift approximant to `ℂ` agrees exactly with evaluating
the complex approximant at the corresponding real shift. -/
theorem ofReal_fabiusDiscreteLimitApproximationReal
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
  rw [← ofReal_fabiusDiscreteLimitApproximationReal]
  exact Complex.ofReal_re _

/-- Real-shift discrete-limit approximants converge on the whole real line. -/
theorem fabiusDiscreteLimitApproximationReal_tendsto_globalFabius_all
    (q x : ℝ) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationReal q x n)
      atTop (𝓝 (globalFabius x)) := by
  rcases le_total 0 x with hx | hx
  · exact fabiusDiscreteLimitApproximationReal_tendsto_globalFabius q hx
  · have happ (n : ℕ) :
        fabiusDiscreteLimitApproximationReal q x n = 0 :=
      fabiusDiscreteLimitApproximationReal_eq_zero_of_nonpos q hx n
    have hglobal : globalFabius x = 0 := by
      change extendedFabius fabius x = 0
      exact extendedFabius_eq_zero_of_nonpos fabius fabius_spec hx
    simp [happ, hglobal]

/-- Rational translations, stated first in the original real form. -/
theorem fabiusDiscreteLimitApproximationRat_tendsto_globalFabius
    (q : ℚ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationRat q x n)
      atTop (𝓝 (globalFabius x)) := by
  simpa only [fabiusDiscreteLimitApproximationRat,
    fabiusDiscreteLimitApproximationReal] using
      fabiusDiscreteLimitApproximationReal_tendsto_globalFabius (q : ℝ) hx

/-- Rational translations converge on the whole real line. -/
theorem fabiusDiscreteLimitApproximationRat_tendsto_globalFabius_all
    (q : ℚ) (x : ℝ) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationRat q x n)
      atTop (𝓝 (globalFabius x)) := by
  simpa only [fabiusDiscreteLimitApproximationRat,
    fabiusDiscreteLimitApproximationReal] using
      fabiusDiscreteLimitApproximationReal_tendsto_globalFabius_all
        (q : ℝ) x

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

/-- Fully expanded complex discrete-limit convergence on the whole real
line. -/
theorem fabiusDiscreteLimit_literal_complex_tendsto_globalFabius_all
    (q : ℂ) (x : ℝ) :
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
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all q x

/-- On `[0,1]`, the same limit is the ordinary bounded Fabius function. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_fabiusReal
    (q : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop (𝓝 (fabiusReal fabius x : ℂ)) := by
  rw [← extendedFabius_eq_fabiusReal fabius fabius_spec hx]
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius q hx.1

/-- The arbitrary-real-shift formula converges to the bounded Fabius
function on its fundamental interval. -/
theorem fabiusDiscreteLimitApproximationReal_tendsto_fabiusReal
    (q : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationReal q x n)
      atTop (𝓝 (fabiusReal fabius x)) := by
  rw [← extendedFabius_eq_fabiusReal fabius fabius_spec hx]
  exact fabiusDiscreteLimitApproximationReal_tendsto_globalFabius q hx.1

/-- Rational-shift specialization on the fundamental interval. -/
theorem fabiusDiscreteLimitApproximationRat_tendsto_fabiusReal
    (q : ℚ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationRat q x n)
      atTop (𝓝 (fabiusReal fabius x)) := by
  simpa only [fabiusDiscreteLimitApproximationRat,
    fabiusDiscreteLimitApproximationReal] using
      fabiusDiscreteLimitApproximationReal_tendsto_fabiusReal (q : ℝ) hx

/-- Gaussian-rational-shift specialization on the fundamental interval. -/
theorem fabiusDiscreteLimitApproximationGaussianRat_tendsto_fabiusReal
    (a b : ℚ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto
      (fun n => fabiusDiscreteLimitApproximationGaussianRat a b x n)
      atTop (𝓝 (fabiusReal fabius x : ℂ)) := by
  rw [← extendedFabius_eq_fabiusReal fabius fabius_spec hx]
  exact fabiusDiscreteLimitApproximationGaussianRat_tendsto_globalFabius
    a b hx.1

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

/-- Exact finite telescope written directly with the literal q-binomial--
Thue--Morse summand.  This simultaneously covers real and complex
translations; the remainder is the same signed binary-tail term as in the
analytic telescope. -/
theorem extendedFabius_eq_qBinomial_telescope_add_remainder
    (K : Type*) [RCLike K]
    (F : BoundedFabius) (hF : IsFabius F)
    (q : K) (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (extendedFabius F x : K) =
      (∑ m ∈ Finset.range (N + 1),
        qBinomialFabiusGlobalSummand K q x m) +
      (binaryReductionRemainder F x N : K) := by
  have h := congrArg (fun z : ℝ => (z : K))
    (extendedFabius_eq_globalBinaryReductionSum_add_remainder
      F hF x hx N)
  push_cast at h
  simpa only [qBinomialFabiusGlobalSummand_eq] using h

/-- Canonical complex finite telescope for the user's translation `q`. -/
theorem globalFabius_eq_qBinomial_telescope_add_remainder_complex
    (q : ℂ) (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (globalFabius x : ℂ) =
      (∑ m ∈ Finset.range (N + 1),
        qBinomialFabiusGlobalSummand ℂ q x m) +
      (binaryReductionRemainder fabius x N : ℂ) := by
  exact extendedFabius_eq_qBinomial_telescope_add_remainder
    ℂ fabius fabius_spec q x hx N

/-- Fully expanded finite q-binomial--Thue--Morse telescope. -/
theorem globalFabius_eq_qBinomialThueMorse_telescope_add_remainder_complex
    (q : ℂ) (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (globalFabius x : ℂ) =
      (∑ m ∈ Finset.range (N + 1),
        (-1 : ℂ) ^ thueMorseBit (binaryPrefix x m) *
          (2 * (binaryPreviousPrefix x m : ℂ) -
            (binaryPrefix x m : ℂ)) *
          ((∑ n ∈ Finset.range (m + 1),
              (((((2 : ℝ) ^ (m + 1) * x -
                      2 * (binaryPrefix x m : ℝ) : ℝ) : ℂ) ^ (m - n) /
                  ((m - n).factorial : ℂ)) *
                ((∑ k ∈ Finset.range (n + 1),
                    algebraMap ℚ ℂ
                      (qBinomial n k (1 / 2) /
                        ((4 : ℚ) ^ k.choose 2 *
                          ((n + k).factorial : ℚ))) *
                      ∑ r ∈ Finset.range (2 ^ k),
                        (-1 : ℂ) ^ thueMorseBit r *
                          ((r : ℂ) - (2 : ℂ) ^ k + q) ^ (n + k)) /
                  algebraMap ℚ ℂ
                    ((2 : ℚ) ^ n.choose 2 *
                      qPochhammer (1 / 2) (1 / 2) n)))) /
            (2 : ℂ) ^ (m + 1).choose 2)) +
      (binaryReductionRemainder fabius x N : ℂ) := by
  change (globalFabius x : ℂ) =
    (∑ m ∈ Finset.range (N + 1),
      qBinomialFabiusGlobalSummand ℂ q x m) +
    (binaryReductionRemainder fabius x N : ℂ)
  exact globalFabius_eq_qBinomial_telescope_add_remainder_complex
    q x hx N

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
