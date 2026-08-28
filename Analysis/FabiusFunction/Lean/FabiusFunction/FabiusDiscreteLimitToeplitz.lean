import FabiusFunction.FabiusRawQBinomialFormula
import FabiusFunction.GeometricLagrange
import FabiusFunction.GeometricRichardson
import FabiusFunction.GeometricQBinomialLagrange
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Toeplitz weights for the Fabius discrete limit

This module packages the finite q-binomial coefficients that arise after
reindexing the proposed discrete-limit formula.  It identifies the complete
row generating polynomial and its dyadic roots, derives exact q-Richardson
cancellation for sequences in arbitrary `ℚ`-modules, and proves quantitative
row estimates.  The normalized
generating polynomial is

`W_n(z) = (z / 2; 1 / 2)_n / (1 / 2; 1 / 2)_n`.

Thus every row has mass one, while `W_n(2^r) = 0` for `1 ≤ r ≤ n`.
These roots make the row an exact Richardson extrapolator for the first `n`
inverse-dyadic correction terms.  Evaluating instead at `z = -2` gives the
weighted variation

`H_n = ∑_j |w_{n,j}| 2^j = (-1; 1 / 2)_n / (1 / 2; 1 / 2)_n`,

and a head-shift identity bounds `H_n` uniformly by `64`.  The unweighted
total variation has its sharper uniform bound `16`.  The module also supplies
a general finite-row Toeplitz convergence theorem and casts the row mass and
norm estimates into arbitrary `RCLike` fields.

The algebraic row is also identified pointwise with the Lagrange evaluation
weights on the reversed geometric grid `1, 1/2, ..., (1/2)^n`.  Consequently
the q-Richardson theorem is a direct specialization of the field-generic
Gaussian closed form in `GeometricQBinomialLagrange` and the module-generic
engine in `GeometricLagrange`.  The same bridge evaluates every positive
reversed-row moment, including all residuals beyond the cancellation range.

The range-length convention uses a half-cell correction.  In particular it
continues to encode the original inclusive upper bound when that bound is
negative, without introducing an ill-formed finite range.

Finite rows genuinely retain the translation parameter.  At depth one and
`x = 1 / 3`, the generic `RCLike` approximant is the quadratic
`q ^ 2 / 2 - q / 3 + 2 / 9`; in particular its real values at `q = 0` and
`q = 1` are different.  The companion integration module proves that this
finite dependence disappears pairwise in the limit.

## Main results

* `discreteLimitWeightPolynomial_eval` and
  `discreteLimitWeightPolynomial_eq_product` identify the normalized row
  polynomial.
* `discreteLimitWeightPolynomial_two_pow_eq_zero` and
  `sum_discreteLimitWeight_mul_two_pow_eq_zero` record its dyadic roots.
* `sum_abs_discreteLimitWeight` and
  `sum_abs_discreteLimitWeight_mul_two_pow` compute the ordinary and dyadically
  weighted variations; their uniform bounds are `16` and `64`.
* `tendsto_weighted_rows_of_tendsto` is the abstract finite-row Toeplitz
  convergence theorem used by the discrete-limit integration layer.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Finset Filter

namespace Fabius

noncomputable section

/-- Number of terms in the inner prefix at scale `p`.  On nonnegative inputs
this is nearest-integer rounding with half-integers rounded upward; on negative
inputs the natural-valued floor clamps the result to zero. -/
def fabiusDiscreteLimitRangeLength (x : ℝ) (p : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ p * x + 1 / 2⌋₊

/-- The range length is the successor of the user's inclusive Wolfram upper
bound `Floor[2^p*x-1/2]`.  Thus `range length` is exactly the safe Lean
encoding of that sum, including the empty case where the upper bound is `-1`. -/
theorem fabiusDiscreteLimitRangeLength_eq_floor_add_one
    {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    (fabiusDiscreteLimitRangeLength x p : ℤ) =
      ⌊(2 : ℝ) ^ p * x - 1 / 2⌋ + 1 := by
  rw [fabiusDiscreteLimitRangeLength]
  have hnonneg : 0 ≤ (2 : ℝ) ^ p * x + 1 / 2 := by positivity
  rw [Int.natCast_floor_eq_floor hnonneg]
  rw [show (2 : ℝ) ^ p * x + 1 / 2 =
      ((2 : ℝ) ^ p * x - 1 / 2) + 1 by ring,
    Int.floor_add_one]

/-- The inner prefix at scale `p` is empty exactly when the scaled
argument `2 ^ p * x` is strictly below `1 / 2`.  Stated for every
real `x`, with no sign hypothesis. -/
theorem fabiusDiscreteLimitRangeLength_eq_zero_iff
    (x : ℝ) (p : ℕ) :
    fabiusDiscreteLimitRangeLength x p = 0 ↔
      (2 : ℝ) ^ p * x < 1 / 2 := by
  rw [fabiusDiscreteLimitRangeLength, Nat.floor_eq_zero]
  constructor <;> intro h <;> linarith

/-- Direct form of the exact empty-prefix criterion. -/
theorem fabiusDiscreteLimitRangeLength_eq_zero_of_lt_half
    {x : ℝ} (p : ℕ) (hx : (2 : ℝ) ^ p * x < 1 / 2) :
    fabiusDiscreteLimitRangeLength x p = 0 :=
  (fabiusDiscreteLimitRangeLength_eq_zero_iff x p).2 hx

/-- At every scale the corrected prefix is empty at and to the left of the
origin. -/
theorem fabiusDiscreteLimitRangeLength_eq_zero_of_nonpos
    {x : ℝ} (hx : x ≤ 0) (p : ℕ) :
    fabiusDiscreteLimitRangeLength x p = 0 := by
  apply fabiusDiscreteLimitRangeLength_eq_zero_of_lt_half p
  have hscale : (2 : ℝ) ^ p * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
  linarith

/-- The prefix is nonempty exactly when the scaled argument reaches the
left edge of the centered half-cell. -/
theorem fabiusDiscreteLimitRangeLength_pos_iff
    (x : ℝ) (p : ℕ) :
    0 < fabiusDiscreteLimitRangeLength x p ↔
      1 / 2 ≤ (2 : ℝ) ^ p * x := by
  simpa only [Nat.pos_iff_ne_zero, not_lt] using
    not_congr (fabiusDiscreteLimitRangeLength_eq_zero_iff x p)

/-- The literal finite expression inside the user's `DiscreteLimit`.  The
inner finite range has length `floor(2^(n+k)*x+1/2)`, equivalently inclusive
upper endpoint `floor(2^(n+k)*x-1/2)` when `x ≥ 0`. -/
def fabiusDiscreteLimitApproximation
    (K : Type*) [RCLike K] (q : K) (x : ℝ) (n : ℕ) : K :=
  (1 / ((2 : K) ^ (n ^ 2) * (halfQPochhammer n : K))) *
    ∑ k ∈ Finset.range (n + 1),
      ((halfQBinomial n k : K) /
          ((4 : K) ^ k.choose 2 * ((n + k).factorial : K))) *
        ∑ r ∈ Finset.range (fabiusDiscreteLimitRangeLength x (n + k)),
          (-1 : K) ^ thueMorseBit r *
            ((r : K) - (2 : K) ^ (n + k) * (x : K) + q) ^ (n + k)

/-- Rational translation, evaluated in the real scalar field. -/
def fabiusDiscreteLimitApproximationRat
    (q : ℚ) (x : ℝ) (n : ℕ) : ℝ :=
  fabiusDiscreteLimitApproximation ℝ (q : ℝ) x n

/-- A translation in the Gaussian rationals, evaluated in `ℂ`. -/
def fabiusDiscreteLimitApproximationGaussianRat
    (a b : ℚ) (x : ℝ) (n : ℕ) : ℂ :=
  fabiusDiscreteLimitApproximation ℂ
    ((a : ℂ) + (b : ℂ) * Complex.I) x n

/-- Arbitrary real translation. -/
def fabiusDiscreteLimitApproximationReal
    (q x : ℝ) (n : ℕ) : ℝ :=
  fabiusDiscreteLimitApproximation ℝ q x n

/-- Arbitrary complex translation. -/
def fabiusDiscreteLimitApproximationComplex
    (q : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  fabiusDiscreteLimitApproximation ℂ q x n

/-- At depth one and `x = 1 / 3`, the translated approximant over any
`RCLike` field is an explicit quadratic in the translation parameter.  This
concrete nonconstant row is the finite-stage counterpart to the
asymptotic shift-independence proved in `FabiusDiscreteLimitIntegration`. -/
theorem fabiusDiscreteLimitApproximation_one_third_depth_one
    (K : Type*) [RCLike K] (q : K) :
    fabiusDiscreteLimitApproximation K q (1 / 3 : ℝ) 1 =
      q ^ 2 / 2 - q / 3 + 2 / 9 := by
  have hlen_one :
      fabiusDiscreteLimitRangeLength (1 / 3 : ℝ) 1 = 1 := by
    rw [fabiusDiscreteLimitRangeLength,
      Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 1 * (1 / 3) + 1 / 2)]
    norm_num
  have hlen_two :
      fabiusDiscreteLimitRangeLength (1 / 3 : ℝ) 2 = 1 := by
    rw [fabiusDiscreteLimitRangeLength,
      Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2 * (1 / 3) + 1 / 2)]
    norm_num
  have hpochhammer : halfQPochhammer 1 = (1 / 2 : ℚ) := by
    norm_num [halfQPochhammer_succ]
  have hbit : thueMorseBit 0 = 0 := by
    norm_num [thueMorseBit, binaryWeight, Nat.digits_zero]
  rw [fabiusDiscreteLimitApproximation]
  norm_num [hlen_one, hlen_two, hpochhammer, hbit,
    Finset.sum_range_succ]
  push_cast
  ring

/-- With zero translation, the depth-one row at `x = 1 / 3` equals
`2 / 9`. -/
@[simp] theorem fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one :
    fabiusDiscreteLimitApproximationReal 0 (1 / 3 : ℝ) 1 = 2 / 9 := by
  rw [fabiusDiscreteLimitApproximationReal,
    fabiusDiscreteLimitApproximation_one_third_depth_one]
  norm_num

/-- With unit translation, the depth-one row at `x = 1 / 3` equals
`7 / 18`. -/
@[simp] theorem fabiusDiscreteLimitApproximationReal_one_one_third_depth_one :
    fabiusDiscreteLimitApproximationReal 1 (1 / 3 : ℝ) 1 = 7 / 18 := by
  rw [fabiusDiscreteLimitApproximationReal,
    fabiusDiscreteLimitApproximation_one_third_depth_one]
  norm_num

/-- The depth-one real approximant at `x = 1 / 3` genuinely depends on its
translation parameter: the zero and unit translations give unequal rows. -/
theorem
    fabiusDiscreteLimitApproximationReal_zero_ne_one_at_one_third_depth_one :
    fabiusDiscreteLimitApproximationReal 0 (1 / 3 : ℝ) 1 ≠
      fabiusDiscreteLimitApproximationReal 1 (1 / 3 : ℝ) 1 := by
  rw [fabiusDiscreteLimitApproximationReal_zero_one_third_depth_one,
    fabiusDiscreteLimitApproximationReal_one_one_third_depth_one]
  norm_num

/-- Every inner prefix in the generic discrete-limit approximant is empty
at and to the left of the origin. -/
theorem fabiusDiscreteLimitApproximation_eq_zero_of_nonpos
    (K : Type*) [RCLike K] (q : K) {x : ℝ} (hx : x ≤ 0) (n : ℕ) :
    fabiusDiscreteLimitApproximation K q x n = 0 := by
  simp [fabiusDiscreteLimitApproximation,
    fabiusDiscreteLimitRangeLength_eq_zero_of_nonpos hx]

/-- Negative-input specialization of the generic vanishing theorem. -/
theorem fabiusDiscreteLimitApproximation_eq_zero_of_neg
    (K : Type*) [RCLike K] (q : K) {x : ℝ} (hx : x < 0) (n : ℕ) :
    fabiusDiscreteLimitApproximation K q x n = 0 :=
  fabiusDiscreteLimitApproximation_eq_zero_of_nonpos K q hx.le n

/-- Real-shift approximants vanish at and to the left of the origin. -/
theorem fabiusDiscreteLimitApproximationReal_eq_zero_of_nonpos
    (q : ℝ) {x : ℝ} (hx : x ≤ 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationReal q x n = 0 := by
  simpa only [fabiusDiscreteLimitApproximationReal] using
    fabiusDiscreteLimitApproximation_eq_zero_of_nonpos ℝ q hx n

/-- Real-shift approximants vanish on the negative axis. -/
theorem fabiusDiscreteLimitApproximationReal_eq_zero_of_neg
    (q : ℝ) {x : ℝ} (hx : x < 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationReal q x n = 0 :=
  fabiusDiscreteLimitApproximationReal_eq_zero_of_nonpos q hx.le n

/-- Complex-shift approximants vanish at and to the left of the origin. -/
theorem fabiusDiscreteLimitApproximationComplex_eq_zero_of_nonpos
    (q : ℂ) {x : ℝ} (hx : x ≤ 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationComplex q x n = 0 := by
  simpa only [fabiusDiscreteLimitApproximationComplex] using
    fabiusDiscreteLimitApproximation_eq_zero_of_nonpos ℂ q hx n

/-- Complex-shift approximants vanish on the negative axis. -/
theorem fabiusDiscreteLimitApproximationComplex_eq_zero_of_neg
    (q : ℂ) {x : ℝ} (hx : x < 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationComplex q x n = 0 :=
  fabiusDiscreteLimitApproximationComplex_eq_zero_of_nonpos q hx.le n

/-- Rational-shift approximants vanish at and to the left of the origin. -/
theorem fabiusDiscreteLimitApproximationRat_eq_zero_of_nonpos
    (q : ℚ) {x : ℝ} (hx : x ≤ 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationRat q x n = 0 := by
  simpa only [fabiusDiscreteLimitApproximationRat] using
    fabiusDiscreteLimitApproximation_eq_zero_of_nonpos ℝ (q : ℝ) hx n

/-- Rational-shift approximants vanish on the negative axis. -/
theorem fabiusDiscreteLimitApproximationRat_eq_zero_of_neg
    (q : ℚ) {x : ℝ} (hx : x < 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationRat q x n = 0 :=
  fabiusDiscreteLimitApproximationRat_eq_zero_of_nonpos q hx.le n

/-- Gaussian-rational-shift approximants vanish at and to the left of the
origin. -/
theorem fabiusDiscreteLimitApproximationGaussianRat_eq_zero_of_nonpos
    (a b : ℚ) {x : ℝ} (hx : x ≤ 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationGaussianRat a b x n = 0 := by
  simpa only [fabiusDiscreteLimitApproximationGaussianRat] using
    fabiusDiscreteLimitApproximation_eq_zero_of_nonpos ℂ
      ((a : ℂ) + (b : ℂ) * Complex.I) hx n

/-- Gaussian-rational-shift approximants vanish on the negative axis. -/
theorem fabiusDiscreteLimitApproximationGaussianRat_eq_zero_of_neg
    (a b : ℚ) {x : ℝ} (hx : x < 0) (n : ℕ) :
    fabiusDiscreteLimitApproximationGaussianRat a b x n = 0 :=
  fabiusDiscreteLimitApproximationGaussianRat_eq_zero_of_nonpos a b hx.le n

/-- The outer Toeplitz weight obtained by putting `j = n-k` in the user's
q-binomial approximant. -/
def discreteLimitWeight (n j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * halfQBinomial n j *
      (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
    halfQPochhammer n

/-- The generating polynomial of a Toeplitz row is a normalized finite
q-Pochhammer product.  Thus the mass, root locus, and Richardson cancellation
of the row are all specializations of one half-q-binomial identity. -/
theorem sum_range_discreteLimitWeight_mul_pow (n : ℕ) (z : ℚ) :
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeight n j * z ^ j) =
      finiteQPochhammer (z / 2) (1 / 2) n / halfQPochhammer n := by
  calc
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeight n j * z ^ j) =
        (∑ j ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ j * (1 / 2 : ℚ) ^ j.choose 2 *
          halfQBinomial n j * (z / 2) ^ j) /
          halfQPochhammer n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _hj
      have hzpow :
          (z / 2 : ℚ) ^ j = (1 / 2 : ℚ) ^ j * z ^ j := by
        rw [show z / 2 = (1 / 2 : ℚ) * z by ring, mul_pow]
      rw [discreteLimitWeight, choose_succ_two, pow_add, hzpow]
      ring
    _ = finiteQPochhammer (z / 2) (1 / 2) n /
          halfQPochhammer n := by
      rw [halfQBinomial_theorem]

/-- The normalized generating polynomial of the `n`-th Toeplitz row:
`W_n(z) = ∑_{j=0}^n w_{n,j} z^j`. -/
noncomputable def discreteLimitWeightPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial j (discreteLimitWeight n j)

/-- Evaluation of the normalized row polynomial:
`W_n(z) = (z / 2; 1 / 2)_n / (1 / 2; 1 / 2)_n`. -/
@[simp] theorem discreteLimitWeightPolynomial_eval (n : ℕ) (z : ℚ) :
    (discreteLimitWeightPolynomial n).eval z =
      finiteQPochhammer (z / 2) (1 / 2) n / halfQPochhammer n := by
  simpa only [discreteLimitWeightPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial] using
    sum_range_discreteLimitWeight_mul_pow n z

private theorem geometricRootPolynomial_half_eval_one (n : ℕ) :
    (geometricRootPolynomial (1 / 2 : ℚ) n).eval 1 =
      halfQPochhammer n := by
  rw [geometricRootPolynomial_eval_one]
  unfold halfQPochhammer finiteQPochhammer
  apply Finset.prod_congr rfl
  intro r _hr
  rw [pow_succ]
  ring

/-- The Toeplitz row polynomial is the half-base specialization of the
general normalized geometric-root polynomial.  This is the structural bridge
between the Fabius q-binomial row and arbitrary-base Richardson filters. -/
theorem discreteLimitWeightPolynomial_eq_normalizedGeometricRootPolynomial
    (n : ℕ) :
    discreteLimitWeightPolynomial n =
      normalizedGeometricRootPolynomial (1 / 2 : ℚ) n := by
  apply Polynomial.funext
  intro z
  rw [discreteLimitWeightPolynomial_eval,
    normalizedGeometricRootPolynomial_eval,
    geometricRootPolynomial_half_eval_one, finiteQPochhammer,
    geometricRootPolynomial_eval]
  congr 1
  apply Finset.prod_congr rfl
  intro r _hr
  rw [pow_succ]
  ring

/-- Product form of the normalized row polynomial.  Its factors exhibit the
simple dyadic roots `2, 4, ..., 2^n` before any evaluation argument. -/
theorem discreteLimitWeightPolynomial_eq_product (n : ℕ) :
    discreteLimitWeightPolynomial n =
      Polynomial.C ((halfQPochhammer n)⁻¹) *
        ∏ r ∈ Finset.range n,
          (1 - Polynomial.C ((1 / 2 : ℚ) ^ (r + 1)) * Polynomial.X) := by
  rw [discreteLimitWeightPolynomial_eq_normalizedGeometricRootPolynomial,
    normalizedGeometricRootPolynomial,
    geometricRootPolynomial_half_eval_one, geometricRootPolynomial]
  ring

/-- Every dyadic node `2^r` with `1 ≤ r ≤ n` is a root of the normalized
row polynomial `W_n`. -/
theorem discreteLimitWeightPolynomial_two_pow_eq_zero
    {n r : ℕ} (hr0 : 1 ≤ r) (hrn : r ≤ n) :
    (discreteLimitWeightPolynomial n).eval ((2 : ℚ) ^ r) = 0 := by
  rw [discreteLimitWeightPolynomial_eq_normalizedGeometricRootPolynomial]
  apply normalizedGeometricRootPolynomial_eval_eq_zero_of_mul_eq_one
    (1 / 2 : ℚ) (r := r - 1)
  · omega
  · rw [show r - 1 + 1 = r by omega, ← mul_pow]
    norm_num

/-- Sum-facing form of the dyadic root identity: the `r`-th geometric mode
`j ↦ (2^r)^j` is annihilated whenever `1 ≤ r ≤ n`. -/
theorem sum_discreteLimitWeight_mul_two_pow_eq_zero
    {n r : ℕ} (hr0 : 1 ≤ r) (hrn : r ≤ n) :
    (∑ j ∈ Finset.range (n + 1),
      discreteLimitWeight n j * ((2 : ℚ) ^ r) ^ j) = 0 := by
  have hroot :=
    discreteLimitWeightPolynomial_two_pow_eq_zero hr0 hrn
  simpa only [discreteLimitWeightPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial] using hroot

/-- Every Toeplitz row has mass one.  This is the value at `z = 1` of
`sum_range_discreteLimitWeight_mul_pow`. -/
theorem sum_range_discreteLimitWeight (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeight n j) = 1 := by
  have h := sum_range_discreteLimitWeight_mul_pow n 1
  rw [show finiteQPochhammer ((1 : ℚ) / 2) (1 / 2) n =
      halfQPochhammer n by rfl,
    div_self (halfQPochhammer_ne_zero n)] at h
  simpa using h

/-- Among rational arguments, the generating polynomial of the `n`-th
Toeplitz row vanishes exactly at the dyadic nodes `2, 4, ..., 2 ^ n`.  The
index `r < n` below records the same root as `2 ^ (r + 1)`. -/
theorem sum_range_discreteLimitWeight_mul_pow_eq_zero_iff
    (n : ℕ) (z : ℚ) :
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeight n j * z ^ j) = 0 ↔
      ∃ r < n, z = (2 : ℚ) ^ (r + 1) := by
  rw [sum_range_discreteLimitWeight_mul_pow, div_eq_zero_iff]
  simp only [halfQPochhammer_ne_zero n, or_false]
  rw [finiteQPochhammer_half_eq_zero_iff]
  constructor
  · rintro ⟨r, hr, hz⟩
    refine ⟨r, hr, ?_⟩
    calc
      z = (z / 2) * 2 := by ring
      _ = (2 : ℚ) ^ r * 2 := by rw [hz]
      _ = (2 : ℚ) ^ (r + 1) := by rw [pow_succ]
  · rintro ⟨r, hr, hz⟩
    refine ⟨r, hr, ?_⟩
    calc
      z / 2 = (2 : ℚ) ^ (r + 1) / 2 := by rw [hz]
      _ = (2 : ℚ) ^ r := by rw [pow_succ]; ring

/-- Moving a reversed dyadic node from the denominator to the numerator.
This is the elementary factorization behind the Toeplitz/Lagrange bridge. -/
private theorem half_pow_sub_mul_eq
    (n j d : ℕ) (hj : j ≤ n) :
    (1 / 2 : ℚ) ^ ((n - j) * d) =
      (1 / 2 : ℚ) ^ (n * d) * ((2 : ℚ) ^ d) ^ j := by
  have hexponents : (n - j) * d + d * j = n * d := by
    rw [Nat.mul_comm d j, ← Nat.add_mul, Nat.sub_add_cancel hj]
  have hinverse :
      ((2 : ℚ) ^ d) ^ j * (1 / 2 : ℚ) ^ (d * j) = 1 := by
    calc
      ((2 : ℚ) ^ d) ^ j * (1 / 2 : ℚ) ^ (d * j) =
          (2 : ℚ) ^ (d * j) * (1 / 2 : ℚ) ^ (d * j) := by
        rw [← pow_mul]
      _ = ((2 : ℚ) * (1 / 2 : ℚ)) ^ (d * j) := by rw [mul_pow]
      _ = 1 := by norm_num
  calc
    (1 / 2 : ℚ) ^ ((n - j) * d) =
        (1 / 2 : ℚ) ^ ((n - j) * d) * 1 := by ring
    _ = (1 / 2 : ℚ) ^ ((n - j) * d) *
        (((2 : ℚ) ^ d) ^ j * (1 / 2 : ℚ) ^ (d * j)) := by
      rw [hinverse]
    _ = ((1 / 2 : ℚ) ^ ((n - j) * d) *
        (1 / 2 : ℚ) ^ (d * j)) * ((2 : ℚ) ^ d) ^ j := by ring
    _ = (1 / 2 : ℚ) ^ (n * d) * ((2 : ℚ) ^ d) ^ j := by
      rw [← pow_add, hexponents]

/-- **Exact reversed moments of a Toeplitz row.**  Reversing the `n`-th
Toeplitz row turns its degree-`d` moment on the half-geometric grid into the
row generating polynomial evaluated at `2^d`, with the common scale
`(1/2)^(nd)` pulled out.  This holds for every `n,d`, not only in the
vanishing range. -/
theorem sum_range_discreteLimitWeight_reverse_mul_half_pow
    (n d : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      discreteLimitWeight n (n - k) * (1 / 2 : ℚ) ^ (k * d)) =
      (1 / 2 : ℚ) ^ (n * d) *
        (finiteQPochhammer ((2 : ℚ) ^ d / 2) (1 / 2) n /
          halfQPochhammer n) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        discreteLimitWeight n (n - k) * (1 / 2 : ℚ) ^ (k * d)) =
        ∑ j ∈ Finset.range (n + 1),
          discreteLimitWeight n j * (1 / 2 : ℚ) ^ ((n - j) * d) := by
      rw [← Finset.sum_range_reflect
        (fun j => discreteLimitWeight n j *
          (1 / 2 : ℚ) ^ ((n - j) * d)) (n + 1)]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - 1 - k = n - k by omega,
        Nat.sub_sub_self hkle]
    _ = (1 / 2 : ℚ) ^ (n * d) *
        ∑ j ∈ Finset.range (n + 1),
          discreteLimitWeight n j * ((2 : ℚ) ^ d) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [half_pow_sub_mul_eq n j d
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
      ring
    _ = (1 / 2 : ℚ) ^ (n * d) *
        (finiteQPochhammer ((2 : ℚ) ^ d / 2) (1 / 2) n /
          halfQPochhammer n) := by
      rw [sum_range_discreteLimitWeight_mul_pow]

/-- The reversed Toeplitz row has exactly the evaluation-at-zero moments on
the grid `1,(1/2),...,(1/2)^n`: mass one in degree zero and vanishing moments
in every positive degree through `n`. -/
theorem sum_range_discreteLimitWeight_reverse_moment
    (n d : ℕ) (hd : d ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      discreteLimitWeight n (n - k) * ((1 / 2 : ℚ) ^ k) ^ d) =
      (0 : ℚ) ^ d := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        discreteLimitWeight n (n - k) * ((1 / 2 : ℚ) ^ k) ^ d) =
        ∑ k ∈ Finset.range (n + 1),
          discreteLimitWeight n (n - k) * (1 / 2 : ℚ) ^ (k * d) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [pow_mul]
    _ = (0 : ℚ) ^ d := by
      rw [sum_range_discreteLimitWeight_reverse_mul_half_pow]
      by_cases hd0 : d = 0
      · subst d
        simp only [Nat.mul_zero, pow_zero, one_mul]
        change halfQPochhammer n / halfQPochhammer n = 1
        exact div_self (halfQPochhammer_ne_zero n)
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
        have hr : r < n := by omega
        have hnum :
            finiteQPochhammer ((2 : ℚ) ^ (r + 1) / 2) (1 / 2) n = 0 := by
          rw [finiteQPochhammer_half_eq_zero_iff]
          exact ⟨r, hr, by rw [pow_succ]; ring⟩
        rw [hnum, zero_div, mul_zero, zero_pow (Nat.succ_ne_zero r)]

/-- **Toeplitz weights are geometric Lagrange weights.**  The `j`-th
coefficient of the `n`-th Fabius Toeplitz row is exactly the evaluation-at-
zero Lagrange weight belonging to the reversed node `(1/2)^(n-j)`.

This conceptual identification includes `n=j=0`; its proof uses only the
generic Gaussian/Lagrange closed form, specialized at the half base. -/
theorem discreteLimitWeight_eq_geometricLagrangeWeight
    {n j : ℕ} (hj : j ≤ n) :
    discreteLimitWeight n j =
      geometricLagrangeWeight (1 / 2 : ℚ) n (n - j) := by
  have hnode :
      Set.InjOn (fun k : ℕ => (1 / 2 : ℚ) ^ k)
        (Finset.range (n + 1)) :=
    (pow_right_injective₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)).injOn
  calc
    discreteLimitWeight n j =
        geometricQBinomialWeightNumerator (1 / 2 : ℚ) n (n - j) /
          finiteQPochhammerIn (1 / 2 : ℚ) (1 / 2 : ℚ) n := by
      simp only [discreteLimitWeight,
        geometricQBinomialWeightNumerator_eq_of_le
          (1 / 2 : ℚ) (Nat.sub_le n j),
        Nat.sub_sub_self hj, gaussianBinomial_half_eq_halfQBinomial,
        finiteQPochhammerIn_rat_eq, halfQPochhammer]
      ring
    _ = geometricLagrangeWeight (1 / 2 : ℚ) n (n - j) :=
      (geometricLagrangeWeight_eq_gaussianBinomial_div
        (1 / 2 : ℚ) n (n - j) hnode (Nat.sub_le n j)).symm

/-- Reverse orientation of `discreteLimitWeight_eq_geometricLagrangeWeight`,
convenient when a geometric sample block is reindexed as a Toeplitz row. -/
theorem geometricLagrangeWeight_half_eq_discreteLimitWeight
    {n k : ℕ} (hk : k ≤ n) :
    geometricLagrangeWeight (1 / 2 : ℚ) n k =
      discreteLimitWeight n (n - k) := by
  simpa only [Nat.sub_sub_self hk] using
    (discreteLimitWeight_eq_geometricLagrangeWeight
      (n := n) (j := n - k) (Nat.sub_le n k)).symm

/-- **Complete positive moments of the reversed Toeplitz row.**  Beyond the
cancelled range, every residual moment remains one half-Gaussian
coefficient.  For `0 < d`,

`sum_k d[n,n-k] ((1/2)^k)^d =
  (-1)^n (1/2)^(n(n+1)/2) halfQBinomial (d-1) n`.

Thus `d ≤ n` recovers cancellation and `d = n + 1` gives the first
surviving moment; the statement also includes `n = 0`. -/
theorem sum_range_discreteLimitWeight_reverse_moment_eq_halfQBinomial
    (n d : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.range (n + 1),
      discreteLimitWeight n (n - k) * ((1 / 2 : ℚ) ^ k) ^ d) =
      (-1 : ℚ) ^ n * (1 / 2 : ℚ) ^ (n * (n + 1) / 2) *
        halfQBinomial (d - 1) n := by
  have hnode :
      Set.InjOn (fun k : ℕ => (1 / 2 : ℚ) ^ k)
        (Finset.range (n + 1)) :=
    (pow_right_injective₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)).injOn
  calc
    (∑ k ∈ Finset.range (n + 1),
        discreteLimitWeight n (n - k) * ((1 / 2 : ℚ) ^ k) ^ d) =
        ∑ k ∈ Finset.range (n + 1),
          geometricLagrangeWeight (1 / 2 : ℚ) n k *
            ((1 / 2 : ℚ) ^ k) ^ d := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [geometricLagrangeWeight_half_eq_discreteLimitWeight
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    _ = (-1 : ℚ) ^ n * (1 / 2 : ℚ) ^ (n * (n + 1) / 2) *
          halfQBinomial (d - 1) n := by
      simpa only [gaussianBinomial_half_eq_halfQBinomial] using
        sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial
          (1 / 2 : ℚ) n d hnode hd

/-- Reindexing a Toeplitz row turns it into the corresponding geometric
Lagrange row on any module-valued sample block.  No module laws beyond the
existence of scalar multiplication are needed for this finite identity. -/
theorem sum_range_discreteLimitWeight_smul_eq_geometricLagrangeWeight
    {M : Type*} [AddCommMonoid M] [SMul ℚ M]
    (n start : ℕ) (u : ℕ → M) :
    (∑ j ∈ Finset.range (n + 1),
      discreteLimitWeight n j • u (start + (n - j))) =
      ∑ k ∈ Finset.range (n + 1),
        geometricLagrangeWeight (1 / 2 : ℚ) n k • u (start + k) := by
  rw [← Finset.sum_range_reflect
    (fun k => geometricLagrangeWeight (1 / 2 : ℚ) n k •
      u (start + k)) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega,
    ← discreteLimitWeight_eq_geometricLagrangeWeight hjle]

/-- A Toeplitz row annihilates each dyadic geometric mode below its order,
after the scalar coefficient of that mode acts on an arbitrary vector in a
`ℚ`-module.  This is the reusable linear core of exact q-Richardson
cancellation. -/
theorem sum_range_discreteLimitWeight_mul_geometricMode_smul_eq_zero
    {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (n r : ℕ) (hr : r < n) (v : M) :
    (∑ j ∈ Finset.range (n + 1),
      (discreteLimitWeight n j *
        (1 / 2 : ℚ) ^ ((r + 1) * (2 * n - j))) • v) = 0 := by
  rw [show (∑ j ∈ Finset.range (n + 1),
      (discreteLimitWeight n j *
        (1 / 2 : ℚ) ^ ((r + 1) * (2 * n - j))) • v) =
      ∑ j ∈ Finset.range (n + 1), discreteLimitWeight n j •
        ((1 / 2 : ℚ) ^ ((r + 1) * (n + (n - j))) • v) by
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [smul_smul, show 2 * n - j = n + (n - j) by omega]]
  rw [sum_range_discreteLimitWeight_smul_eq_geometricLagrangeWeight
    n n (fun p => (1 / 2 : ℚ) ^ ((r + 1) * p) • v)]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]
  have hnode :
      Set.InjOn (fun k : ℕ => (1 / 2 : ℚ) ^ k)
        (Finset.range (n + 1)) :=
    (pow_right_injective₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)).injOn
  have hzero := sum_geometricLagrangeWeight_mul_shifted_pow_eq_zero
    (1 / 2 : ℚ) n n (r + 1) hnode (Nat.succ_pos r)
      (Nat.succ_le_iff.mpr hr)
  have hzero' :
      (∑ k ∈ Finset.range (n + 1),
        geometricLagrangeWeight (1 / 2 : ℚ) n k *
          (1 / 2 : ℚ) ^ ((r + 1) * (n + k))) = 0 := by
    convert hzero using 1
    apply Finset.sum_congr rfl
    intro k _hk
    rw [Nat.mul_comm (r + 1) (n + k), pow_mul]
  rw [hzero', zero_smul]

/-- **Local exact q-Richardson cancellation.**  It is enough for the first
`n` geometric error modes to describe the `n + 1` samples in one block
beginning at an arbitrary `start`; no global formula for the sequence is
needed.  The result is module-valued and includes `n = 0` and `start = 0`. -/
theorem discreteLimitWeight_qRichardson_exact_module_at_of_eq
    {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (n start : ℕ) (u : ℕ → M) (L : M) (a : ℕ → M)
    (hu : ∀ k ∈ Finset.range (n + 1),
      u (start + k) = L + ∑ r ∈ Finset.range n,
        (1 / 2 : ℚ) ^ ((r + 1) * (start + k)) • a r) :
    (∑ j ∈ Finset.range (n + 1),
      discreteLimitWeight n j • u (start + (n - j))) = L := by
  rw [sum_range_discreteLimitWeight_smul_eq_geometricLagrangeWeight]
  have hnode :
      Set.InjOn (fun k : ℕ => (1 / 2 : ℚ) ^ k)
        (Finset.range (n + 1)) :=
    (pow_right_injective₀ (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)).injOn
  apply geometricLagrange_richardson_exact_of_eq
    (1 / 2 : ℚ) n start hnode u L a
  intro k hk
  rw [hu k hk]
  apply congrArg (fun z : M => L + z)
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Nat.mul_comm (r + 1) (start + k), pow_mul]

/-- Exact q-Richardson cancellation on the dyadic geometric grid in an
arbitrary `ℚ`-module.  If a module-valued sequence has error in the span of
the first `n` modes `p ↦ (1 / 2) ^ ((r + 1) * p)`, then the `n`-th Toeplitz
row recovers its constant term exactly. -/
theorem discreteLimitWeight_qRichardson_exact_module
    {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (n : ℕ) (u : ℕ → M) (L : M) (a : ℕ → M)
    (hu : ∀ p, u p =
      L + ∑ r ∈ Finset.range n,
        (1 / 2 : ℚ) ^ ((r + 1) * p) • a r) :
    (∑ j ∈ Finset.range (n + 1),
      discreteLimitWeight n j • u (2 * n - j)) = L := by
  have hexact := discreteLimitWeight_qRichardson_exact_module_at_of_eq
    n n u L a fun k _hk => hu (n + k)
  calc
    (∑ j ∈ Finset.range (n + 1),
        discreteLimitWeight n j • u (2 * n - j)) =
        ∑ j ∈ Finset.range (n + 1),
          discreteLimitWeight n j • u (n + (n - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    _ = L := hexact

/-- Rational specialization of exact q-Richardson cancellation.  If the
error is a linear combination of the first `n` dyadic geometric modes, then
the `n`-th Toeplitz row at the samples `2 * n - j` recovers the constant term
exactly. -/
theorem discreteLimitWeight_qRichardson_exact
    (n : ℕ) (u : ℕ → ℚ) (L : ℚ) (a : ℕ → ℚ)
    (hu : ∀ p, u p =
      L + ∑ r ∈ Finset.range n,
        a r * (1 / 2 : ℚ) ^ ((r + 1) * p)) :
    (∑ j ∈ Finset.range (n + 1),
      discreteLimitWeight n j * u (2 * n - j)) = L := by
  have hu' : ∀ p, u p =
      L + ∑ r ∈ Finset.range n,
        (1 / 2 : ℚ) ^ ((r + 1) * p) • a r := by
    intro p
    calc
      u p = L + ∑ r ∈ Finset.range n,
          a r * (1 / 2 : ℚ) ^ ((r + 1) * p) := hu p
      _ = L + ∑ r ∈ Finset.range n,
          (1 / 2 : ℚ) ^ ((r + 1) * p) • a r := by
        refine congrArg (fun x : ℚ => L + x) ?_
        apply Finset.sum_congr rfl
        intro r _hr
        simpa only [smul_eq_mul] using
          (mul_comm (a r) ((1 / 2 : ℚ) ^ ((r + 1) * p)))
  simpa only [smul_eq_mul] using
    (discreteLimitWeight_qRichardson_exact_module n u L a hu')

private theorem quarter_add_pow_le_halfQPochhammer_succ (n : ℕ) :
    (1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (n + 2) ≤
      halfQPochhammer (n + 1) := by
  induction n with
  | zero => norm_num [halfQPochhammer_succ]
  | succ n ih =>
      rw [halfQPochhammer_succ]
      have hpow_nonneg : 0 ≤ (1 / 2 : ℚ) ^ (n + 2) := by positivity
      have hpow_le : (1 / 2 : ℚ) ^ (n + 2) ≤ 1 / 4 := by
        rw [show n + 2 = 2 + n by omega, pow_add]
        norm_num
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hfac_nonneg : 0 ≤ 1 - (1 / 2 : ℚ) ^ (n + 2) := by linarith
      have hmul := mul_le_mul_of_nonneg_right ih hfac_nonneg
      calc
        (1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (n + 3) ≤
            ((1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (n + 2)) *
              (1 - (1 / 2 : ℚ) ^ (n + 2)) := by
                rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
                nlinarith
        _ ≤ halfQPochhammer (n + 1) *
              (1 - (1 / 2 : ℚ) ^ (n + 2)) := hmul

/-- The finite q-Pochhammer symbol at `q = 1 / 2` is at least
`1 / 4`, uniformly in `n`.  It is used in
`sum_abs_discreteLimitWeight_le` below to bound
`1 / halfQPochhammer n` by `4`. -/
theorem one_fourth_le_halfQPochhammer (n : ℕ) :
    (1 / 4 : ℚ) ≤ halfQPochhammer n := by
  cases n with
  | zero => norm_num
  | succ n =>
      exact le_trans (le_add_of_nonneg_right (by positivity))
        (quarter_add_pow_le_halfQPochhammer_succ n)

private theorem finiteQPochhammer_neg_half_mul_half_le_one (n : ℕ) :
    finiteQPochhammer (-1 / 2) (1 / 2) n * halfQPochhammer n ≤ 1 := by
  rw [finiteQPochhammer, halfQPochhammer, finiteQPochhammer,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_one
  · intro j _hj
    let a : ℚ := (1 / 2 : ℚ) ^ (j + 1)
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hterm :
        (1 - (-1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) *
            (1 - (1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) =
          (1 + a) * (1 - a) := by
      dsimp [a]
      rw [pow_succ]
      ring
    rw [hterm]
    nlinarith
  · intro j _hj
    let a : ℚ := (1 / 2 : ℚ) ^ (j + 1)
    have hsquare : 0 ≤ a ^ 2 := sq_nonneg _
    have hterm :
        (1 - (-1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) *
            (1 - (1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) =
          (1 + a) * (1 - a) := by
      dsimp [a]
      rw [pow_succ]
      ring
    rw [hterm]
    nlinarith

/-- Absolute value of a Toeplitz coefficient within its finite row.  All
factors remaining after removal of the alternating sign are positive. -/
theorem abs_discreteLimitWeight {n j : ℕ} (hj : j ≤ n) :
    |discreteLimitWeight n j| =
      halfQBinomial n j * (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
        halfQPochhammer n := by
  rw [discreteLimitWeight, abs_div, abs_mul, abs_mul, abs_pow, abs_pow]
  rw [abs_of_pos (halfQBinomial_pos hj),
    abs_of_pos (halfQPochhammer_pos n)]
  norm_num

/-- Exact total variation of the `n`-th Toeplitz row.  The coarse uniform
bound below is obtained by estimating the two finite q-Pochhammer factors. -/
theorem sum_abs_discreteLimitWeight (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) =
      finiteQPochhammer (-1 / 2) (1 / 2) n / halfQPochhammer n := by
  have hplus := halfQBinomial_theorem n (-1 / 2)
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
          halfQBinomial n j *
            (1 / 2 : ℚ) ^ ((j + 1).choose 2)) =
        finiteQPochhammer (-1 / 2) (1 / 2) n := by
    rw [← hplus]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [choose_succ_two, pow_add]
    rw [show (-1 / 2 : ℚ) ^ j =
        (-1 : ℚ) ^ j * (1 / 2 : ℚ) ^ j by
          rw [show (-1 / 2 : ℚ) = (-1 : ℚ) * (1 / 2 : ℚ) by norm_num,
            mul_pow]]
    have hsign : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      halfQBinomial n j *
          ((1 / 2 : ℚ) ^ j.choose 2 * (1 / 2 : ℚ) ^ j) =
          ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) *
            (halfQBinomial n j *
              ((1 / 2 : ℚ) ^ j.choose 2 * (1 / 2 : ℚ) ^ j)) := by
            rw [hsign, one_mul]
      _ = _ := by ring
  have hl1 :
      (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) =
        finiteQPochhammer (-1 / 2) (1 / 2) n /
          halfQPochhammer n := by
    calc
      (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) =
          ∑ j ∈ Finset.range (n + 1),
            halfQBinomial n j * (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
              halfQPochhammer n := by
        apply Finset.sum_congr rfl
        intro j hj
        exact abs_discreteLimitWeight
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.sum_div, hsum]
  exact hl1

/-- The dyadically weighted variation of row `n`:
`H_n = (-1; 1 / 2)_n / (1 / 2; 1 / 2)_n`.  The theorem
`sum_abs_discreteLimitWeight_mul_two_pow` identifies this quotient with
`∑_j |w_{n,j}| 2^j`. -/
noncomputable def discreteLimitWeightedVariation (n : ℕ) : ℚ :=
  finiteQPochhammer (-1) (1 / 2) n / halfQPochhammer n

/-- Exact dyadically weighted variation of the `n`-th Toeplitz row:
`∑_{j=0}^n |w_{n,j}| 2^j = H_n`.  Conceptually this is the generating
polynomial identity `W_n(-2) = H_n`: the two alternating signs cancel. -/
theorem sum_abs_discreteLimitWeight_mul_two_pow (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      |discreteLimitWeight n j| * (2 : ℚ) ^ j) =
        discreteLimitWeightedVariation n := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      |discreteLimitWeight n j| * (2 : ℚ) ^ j =
        discreteLimitWeight n j * (-2 : ℚ) ^ j := by
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [abs_discreteLimitWeight hjle, discreteLimitWeight]
    have hneg : (-2 : ℚ) ^ j = (-1 : ℚ) ^ j * (2 : ℚ) ^ j := by
      rw [show (-2 : ℚ) = (-1 : ℚ) * 2 by norm_num, mul_pow]
    have hsign : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hneg]
    calc
      halfQBinomial n j * (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
            halfQPochhammer n * (2 : ℚ) ^ j =
          ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) *
            (halfQBinomial n j * (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
              halfQPochhammer n * (2 : ℚ) ^ j) := by
        rw [hsign, one_mul]
      _ = ((-1 : ℚ) ^ j * halfQBinomial n j *
              (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
            halfQPochhammer n) *
          ((-1 : ℚ) ^ j * (2 : ℚ) ^ j) := by
        ring
  calc
    (∑ j ∈ Finset.range (n + 1),
        |discreteLimitWeight n j| * (2 : ℚ) ^ j) =
        ∑ j ∈ Finset.range (n + 1),
          discreteLimitWeight n j * (-2 : ℚ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j hj
    _ = (discreteLimitWeightPolynomial n).eval (-2) := by
      rw [discreteLimitWeightPolynomial, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_monomial]
    _ = discreteLimitWeightedVariation n := by
      norm_num [discreteLimitWeightedVariation]

/-- Removing the head factor from `(-1; 1 / 2)_(n+1)` leaves twice the
shifted product `(-1 / 2; 1 / 2)_n`.  This is the structural bridge from the
weighted variation `H_(n+1)` to the ordinary variation of row `n`. -/
theorem finiteQPochhammer_neg_one_succ (n : ℕ) :
    finiteQPochhammer (-1) (1 / 2) (n + 1) =
      2 * finiteQPochhammer (-1 / 2) (1 / 2) n := by
  induction n with
  | zero => norm_num [finiteQPochhammer]
  | succ n ih =>
      calc
        finiteQPochhammer (-1) (1 / 2) (n + 1 + 1) =
            finiteQPochhammer (-1) (1 / 2) (n + 1) *
              (1 - (-1) * (1 / 2 : ℚ) ^ (n + 1)) :=
          finiteQPochhammer_succ _ _ _
        _ = 2 * finiteQPochhammer (-1 / 2) (1 / 2) n *
              (1 - (-1) * (1 / 2 : ℚ) ^ (n + 1)) := by
          rw [ih]
        _ = 2 * (finiteQPochhammer (-1 / 2) (1 / 2) n *
              (1 - (-1 / 2) * (1 / 2 : ℚ) ^ n)) := by
          rw [pow_succ]
          ring
        _ = 2 * finiteQPochhammer (-1 / 2) (1 / 2) (n + 1) := by
          rw [finiteQPochhammer_succ]

/-- The total variations of the Toeplitz rows are bounded uniformly in the
row index. -/
theorem sum_abs_discreteLimitWeight_le (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) ≤ 16 := by
  rw [sum_abs_discreteLimitWeight]
  have hp := halfQPochhammer_pos n
  have hpquarter := one_fourth_le_halfQPochhammer n
  have hplus_div :
      finiteQPochhammer (-1 / 2) (1 / 2) n ≤
        1 / halfQPochhammer n := by
    rw [le_div_iff₀ hp]
    exact finiteQPochhammer_neg_half_mul_half_le_one n
  have hinv_le : 1 / halfQPochhammer n ≤ 4 := by
    rw [div_le_iff₀ hp]
    linarith
  calc
    finiteQPochhammer (-1 / 2) (1 / 2) n / halfQPochhammer n ≤
        (1 / halfQPochhammer n) / halfQPochhammer n :=
      div_le_div_of_nonneg_right hplus_div hp.le
    _ = (1 / halfQPochhammer n) ^ 2 := by field_simp
    _ ≤ (4 : ℚ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by norm_num)).2 hinv_le
    _ = 16 := by norm_num

/-- Successor formula for the dyadically weighted variation.  It separates
the head factor `2 / (1 - 2^(-(n+1)))` from the ordinary variation of row
`n`, making the uniform estimate transparent. -/
theorem discreteLimitWeightedVariation_succ (n : ℕ) :
    discreteLimitWeightedVariation (n + 1) =
      (2 / (1 - (1 / 2 : ℚ) ^ (n + 1))) *
        (finiteQPochhammer (-1 / 2) (1 / 2) n / halfQPochhammer n) := by
  have hpow_lt : (1 / 2 : ℚ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hfac : 1 - (1 / 2 : ℚ) ^ (n + 1) ≠ 0 :=
    (sub_pos.mpr hpow_lt).ne'
  rw [discreteLimitWeightedVariation, finiteQPochhammer_neg_one_succ,
    halfQPochhammer_succ]
  field_simp [halfQPochhammer_ne_zero, hfac]
  <;> ring

/-- The dyadically weighted variations satisfy the uniform estimate
`H_n ≤ 64`, including the zeroth row.  For a successor row the head factor
is at most `4`, while the remaining ordinary variation is at most `16`. -/
theorem discreteLimitWeightedVariation_le (n : ℕ) :
    discreteLimitWeightedVariation n ≤ 64 := by
  cases n with
  | zero => norm_num [discreteLimitWeightedVariation, finiteQPochhammer]
  | succ n =>
      rw [discreteLimitWeightedVariation_succ]
      have hpow_le : (1 / 2 : ℚ) ^ (n + 1) ≤ 1 / 2 := by
        rw [show n + 1 = 1 + n by omega, pow_add]
        norm_num
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hfac_pos : 0 < 1 - (1 / 2 : ℚ) ^ (n + 1) := by
        have hpow_lt : (1 / 2 : ℚ) ^ (n + 1) < 1 :=
          pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
        linarith
      have hhead_le :
          2 / (1 - (1 / 2 : ℚ) ^ (n + 1)) ≤ 4 := by
        rw [div_le_iff₀ hfac_pos]
        linarith
      have hvariation_nonneg :
          0 ≤ finiteQPochhammer (-1 / 2) (1 / 2) n /
            halfQPochhammer n := by
        rw [← sum_abs_discreteLimitWeight]
        positivity
      have hvariation_le :
          finiteQPochhammer (-1 / 2) (1 / 2) n /
              halfQPochhammer n ≤ 16 := by
        rw [← sum_abs_discreteLimitWeight]
        exact sum_abs_discreteLimitWeight_le n
      calc
        (2 / (1 - (1 / 2 : ℚ) ^ (n + 1))) *
              (finiteQPochhammer (-1 / 2) (1 / 2) n /
                halfQPochhammer n) ≤
            (4 : ℚ) * 16 :=
          mul_le_mul hhead_le hvariation_le hvariation_nonneg (by norm_num)
        _ = 64 := by norm_num

/-- A finite-row Toeplitz convergence lemma.  The row sums are one, their
total variations are uniformly bounded, and every sampled index in a row
eventually lies in any prescribed tail.  No order or real/complex structure
on the coefficient field is needed. -/
theorem tendsto_weighted_rows_of_tendsto
    {K : Type*} [NormedRing K]
    (w : ℕ → ℕ → K) (index : ℕ → ℕ → ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrow : ∀ n, (∑ j ∈ Finset.range (n + 1), w n j) = 1)
    (hvariation : ∀ n,
      (∑ j ∈ Finset.range (n + 1), ‖w n j‖) ≤ C)
    (hindex : ∀ N, ∃ N₀, ∀ n ≥ N₀, ∀ j ∈ Finset.range (n + 1),
      N ≤ index n j)
    {H : ℕ → K} {L : K} (hH : Tendsto H atTop (𝓝 L)) :
    Tendsto
      (fun n => ∑ j ∈ Finset.range (n + 1),
        w n j * H (index n j))
      atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hH ⊢
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨N, hN⟩ := hH (ε / (C + 1)) (div_pos hε hCp)
  obtain ⟨N₀, hN₀⟩ := hindex N
  refine ⟨N₀, fun n hn => ?_⟩
  have hpoint (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      ‖H (index n j) - L‖ < ε / (C + 1) := by
    have h := hN (index n j) (hN₀ n hn j hj)
    simpa only [dist_eq_norm] using h
  have hdiff :
      (∑ j ∈ Finset.range (n + 1), w n j * H (index n j)) - L =
        ∑ j ∈ Finset.range (n + 1),
          w n j * (H (index n j) - L) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
  rw [dist_eq_norm, hdiff]
  calc
    ‖∑ j ∈ Finset.range (n + 1),
        w n j * (H (index n j) - L)‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖w n j * (H (index n j) - L)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          ‖w n j‖ * ‖H (index n j) - L‖ := by
      apply Finset.sum_le_sum
      intro j _hj
      exact norm_mul_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          ‖w n j‖ * (ε / (C + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hpoint j hj).le (norm_nonneg _)
    _ = (∑ j ∈ Finset.range (n + 1), ‖w n j‖) *
          (ε / (C + 1)) := by rw [Finset.sum_mul]
    _ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_right (hvariation n) (div_nonneg hε.le hCp.le)
    _ = ε * (C / (C + 1)) := by field_simp
    _ < ε * 1 := by
      exact mul_lt_mul_of_pos_left ((div_lt_one hCp).2 (by linarith)) hε
    _ = ε := mul_one ε

/-- The rational Toeplitz weight cast into an `RCLike` field. -/
def discreteLimitWeightIn (K : Type*) [RCLike K] (n j : ℕ) : K :=
  (discreteLimitWeight n j : K)

/-- The norm of a rational Toeplitz weight in any `RCLike` field is the
ordinary absolute value of the rational coefficient, cast to `ℝ`. -/
@[simp] theorem norm_discreteLimitWeightIn
    (K : Type*) [RCLike K] (n j : ℕ) :
    ‖discreteLimitWeightIn K n j‖ = |discreteLimitWeight n j| := by
  rw [discreteLimitWeightIn, ← RCLike.ofReal_ratCast,
    RCLike.norm_ofReal, Rat.cast_abs]

/-- Row mass one after casting the rational weights into an
`RCLike` field. -/
theorem sum_range_discreteLimitWeightIn
    (K : Type*) [RCLike K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeightIn K n j) = 1 := by
  simp_rw [discreteLimitWeightIn]
  rw [← Rat.cast_sum,
    sum_range_discreteLimitWeight]
  norm_num

/-- The cast rows have total variation at most `16`, uniformly in
`n`.  Together with `sum_range_discreteLimitWeightIn` this supplies
the two row hypotheses of `tendsto_weighted_rows_of_tendsto` used
in `tendsto_discreteLimitWeightIn_sum` below. -/
theorem sum_norm_discreteLimitWeightIn_le
    (K : Type*) [RCLike K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ‖discreteLimitWeightIn K n j‖) ≤ 16 := by
  simp_rw [norm_discreteLimitWeightIn]
  exact_mod_cast sum_abs_discreteLimitWeight_le n

/-- Exact dyadically weighted norm sum after casting the rational row into
an arbitrary `RCLike` field.  This is the real-valued form of
`sum_abs_discreteLimitWeight_mul_two_pow` used in quantitative estimates. -/
theorem sum_norm_discreteLimitWeightIn_mul_two_pow
    (K : Type*) [RCLike K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      ‖discreteLimitWeightIn K n j‖ * (2 : ℝ) ^ j) =
        (discreteLimitWeightedVariation n : ℝ) := by
  simp_rw [norm_discreteLimitWeightIn]
  exact_mod_cast sum_abs_discreteLimitWeight_mul_two_pow n

/-- The cast dyadically weighted norm sum is at most `64`, uniformly in the
row and independently of the chosen `RCLike` coefficient field. -/
theorem sum_norm_discreteLimitWeightIn_mul_two_pow_le
    (K : Type*) [RCLike K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      ‖discreteLimitWeightIn K n j‖ * (2 : ℝ) ^ j) ≤ 64 := by
  rw [sum_norm_discreteLimitWeightIn_mul_two_pow]
  exact_mod_cast discreteLimitWeightedVariation_le n

/-- Every index `2n-j` occurring in row `n` is at least `n`. -/
theorem discreteLimit_index_ge {n j : ℕ} (hj : j ∈ Finset.range (n + 1)) :
    n ≤ 2 * n - j := by
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  omega

/-- Specialized Toeplitz convergence for the reindexing `p = 2n-j`. -/
theorem tendsto_discreteLimitWeightIn_sum
    {K : Type*} [RCLike K] {H : ℕ → K} {L : K}
    (hH : Tendsto H atTop (𝓝 L)) :
    Tendsto
      (fun n => ∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * H (2 * n - j))
      atTop (𝓝 L) := by
  apply tendsto_weighted_rows_of_tendsto
    (w := discreteLimitWeightIn K) (index := fun n j => 2 * n - j)
    16 (by norm_num)
    (sum_range_discreteLimitWeightIn K)
    (sum_norm_discreteLimitWeightIn_le K)
    _ hH
  intro N
  exact ⟨N, fun n hn j hj => hn.trans (discreteLimit_index_ge hj)⟩

end

end Fabius
