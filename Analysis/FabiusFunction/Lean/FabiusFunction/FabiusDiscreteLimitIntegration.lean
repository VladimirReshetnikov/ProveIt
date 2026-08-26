import FabiusFunction.FabiusComplexShiftSpline
import FabiusFunction.FabiusDiscreteLimitToeplitz
import FabiusFunction.FabiusGlobalQBinomialSeries

/-!
# The Fabius discrete-limit formula

This module performs the exact outer q-binomial reindexing, applies the
Toeplitz convergence theorem to the complex-shift spline limit, and connects
the resulting limit with the already proved binary telescope and literal
global q-binomial series.  Exact empty-prefix vanishing extends the main
convergence theorem and both final series identifications from the nonnegative
axis to every real input; the older half-line forms remain compatibility APIs.

The shift-independence is asymptotic rather than termwise: any two fixed real
or complex translations become pairwise indistinguishable, although the
depth-one row at `x = 1 / 3` already distinguishes `q = 0` from `q = 1`.
Moreover, at `q = 0` that discrete row differs from the binary—and hence
literal global-q—partial sum at the same outer truncation index `n = N = 1`.
Thus the discrete-limit sequence shares their common limit without agreeing at
every common outer truncation index with those two pointwise-identical
partial-sum constructions.
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

/-- Any two fixed complex translations of the discrete-limit formula become
asymptotically indistinguishable on the whole real line.  This is the precise
limit counterpart to the finite-row dependence exhibited at depth one. -/
theorem fabiusDiscreteLimitApproximationComplex_sub_tendsto_zero_all
    (q₁ q₂ : ℂ) (x : ℝ) :
    Tendsto
      (fun n => fabiusDiscreteLimitApproximationComplex q₁ x n -
        fabiusDiscreteLimitApproximationComplex q₂ x n)
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    (fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all q₁ x).sub
      (fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all q₂ x)

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

/-- Any two fixed real translations of the discrete-limit formula become
asymptotically indistinguishable on the whole real line. -/
theorem fabiusDiscreteLimitApproximationReal_sub_tendsto_zero_all
    (q₁ q₂ x : ℝ) :
    Tendsto
      (fun n => fabiusDiscreteLimitApproximationReal q₁ x n -
        fabiusDiscreteLimitApproximationReal q₂ x n)
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    (fabiusDiscreteLimitApproximationReal_tendsto_globalFabius_all q₁ x).sub
      (fabiusDiscreteLimitApproximationReal_tendsto_globalFabius_all q₂ x)

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

/-- At `x = 1 / 3`, the zero-translation discrete row with outer index `n = 1`
is not the binary partial sum with outer index `N = 1` (through scale one): the
former is `2 / 9`, while both binary summands in the latter vanish.  This gives
an explicit mismatch at the common outer truncation index `n = N = 1`. -/
theorem
    fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one_ne_binaryPartialSum :
    fabiusDiscreteLimitApproximationReal 0 (1 / 3 : ℝ) 1 ≠
      ∑ m ∈ Finset.range 2,
        globalBinaryReductionSummand (1 / 3 : ℝ) m := by
  have hzero :
      globalBinaryReductionSummand (1 / 3 : ℝ) 0 = 0 :=
    globalBinaryReductionSummand_zero_of_lt_one (1 / 3 : ℝ) (by norm_num)
  have hprefix : binaryPrefix (1 / 3 : ℝ) 1 = 0 := by
    rw [binaryPrefix, Nat.floor_eq_zero]
    norm_num
  have hcoefficient :
      globalBinaryReductionCoefficient (1 / 3 : ℝ) 1 = 0 := by
    apply globalBinaryReductionCoefficient_eq_zero_of_mod_two_eq_zero
    simp only [hprefix, Nat.zero_mod]
  have hone :
      globalBinaryReductionSummand (1 / 3 : ℝ) 1 = 0 := by
    rw [globalBinaryReductionSummand, hcoefficient, zero_mul]
  rw [fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, hzero, hone]

/-- The same outer-index-one row also differs from the literal global-q
partial sum over every `RCLike` coefficient field and for every series
parameter `q`.  The real zero-translation row is embedded into that field.
The proof uses the pointwise equality between each global-q summand and its
binary counterpart; it does not assert that those two series differ. -/
theorem
    fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one_ne_qBinomialPartialSum
    (K : Type*) [RCLike K] (q : K) :
    (fabiusDiscreteLimitApproximationReal 0 (1 / 3 : ℝ) 1 : K) ≠
      ∑ m ∈ Finset.range 2,
        qBinomialFabiusGlobalSummand K q (1 / 3 : ℝ) m := by
  intro h
  apply
    fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one_ne_binaryPartialSum
  exact RCLike.ofReal_injective (K := K) (by
    simpa only [RCLike.ofReal_sum,
      qBinomialFabiusGlobalSummand_eq] using h)

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

/-- For every real input, the finite binary telescopes converge to the same
target as the discrete limit.  At a nonpositive input every summand and the
signed global Fabius function vanish exactly. -/
theorem binary_telescope_tendsto_globalFabius_all
    (x : ℝ) :
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.range N,
        globalBinaryReductionSummand x m)
      atTop (𝓝 (globalFabius x)) := by
  simpa only [globalFabius] using
    (hasSum_globalBinaryReductionSummand_all
      fabius fabius_spec x).tendsto_sum_nat

/-- Compatibility form of binary-telescope convergence on the nonnegative
half-line. -/
theorem binary_telescope_tendsto_globalFabius
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.range N,
        globalBinaryReductionSummand x m)
      atTop (𝓝 (globalFabius x)) := by
  simpa only [max_eq_left hx] using
    binary_telescope_tendsto_globalFabius_all (max x 0)

/-- For every real input, the `q`-dependent finite rows converge to the
`q`-independent binary-reduction `tsum`. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_binary_tsum_all
    (q : ℂ) (x : ℝ) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop
      (𝓝 ((↑(∑' m : ℕ, globalBinaryReductionSummand x m) : ℂ))) := by
  rw [← extendedFabius_eq_tsum_globalBinaryReductionSummand_all
    fabius fabius_spec x]
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all q x

/-- Compatibility form of convergence to the `q`-independent
binary-reduction `tsum` on the nonnegative half-line. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_binary_tsum
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop
      (𝓝 ((↑(∑' m : ℕ, globalBinaryReductionSummand x m) : ℂ))) := by
  simpa only [max_eq_left hx] using
    fabiusDiscreteLimitApproximationComplex_tendsto_binary_tsum_all
      q (max x 0)

/-- All-real limit-to-`tsum` form for the fully literal global q-binomial
series. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum_all
    (q : ℂ) (x : ℝ) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop
      (𝓝 (∑' m : ℕ, qBinomialFabiusGlobalSummand ℂ q x m)) := by
  rw [← extendedFabius_eq_tsum_qBinomialFabiusGlobalSummand_all
    ℂ fabius fabius_spec q x]
  exact fabiusDiscreteLimitApproximationComplex_tendsto_globalFabius_all q x

/-- Compatibility limit-to-`tsum` form for the fully literal global
q-binomial series on the nonnegative half-line. -/
theorem fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum
    (q : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => fabiusDiscreteLimitApproximationComplex q x n)
      atTop
      (𝓝 (∑' m : ℕ, qBinomialFabiusGlobalSummand ℂ q x m)) := by
  simpa only [max_eq_left hx] using
    fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum_all
      q (max x 0)

end

end Fabius
