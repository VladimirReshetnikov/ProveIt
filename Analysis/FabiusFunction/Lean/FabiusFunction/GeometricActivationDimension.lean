import FabiusFunction.HyperbolicActivation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric activation dimensions

This module sums the local activation probability along a geometric lattice.
The generic comparison

`activationProbability (q ^ n * t) ≤ (t ^ 2 / 3) * (q ^ 2) ^ n`

gives summability for `|q| < 1` together with the exact geometric-series
budget.  Substituting the normalized scale `(1 - q) * t` produces the
effective dimension of the centered geometric-uniform law,

`geometricActivationDimension q t = ∑' n, activationProbability (q ^ n * ((1 - q) * t))`.

The definition is total in `q`, using Mathlib's convention that the `tsum` of
a nonsummable real family is zero.  Thus only `|q| < 1` carries the intended
convergent-series meaning; the refinement and quantitative estimates use that
hypothesis, and probability-law applications normally further assume
`0 ≤ q < 1`.  At `q = 1 / 2` it is exactly the dyadic effective dimension
from the Fabius/Rvachev active-digit law.
-/

open scoped BigOperators

namespace Fabius

set_option autoImplicit false

noncomputable section

/-! ## A geometric majorant for the local activation probability -/

/-- The quadratic activation bound along a geometric lattice, with the
dependence on the lattice index separated as a power of `q ^ 2`. -/
theorem activationProbability_pow_mul_le (q t : ℝ) (n : ℕ) :
    activationProbability (q ^ n * t) ≤
      (t ^ 2 / 3) * (q ^ 2) ^ n := by
  have hpow : (q ^ n) ^ 2 = (q ^ 2) ^ n := by
    calc
      (q ^ n) ^ 2 = q ^ (n * 2) := (pow_mul q n 2).symm
      _ = q ^ (2 * n) := by rw [Nat.mul_comm]
      _ = (q ^ 2) ^ n := pow_mul q 2 n
  calc
    activationProbability (q ^ n * t) ≤ (q ^ n * t) ^ 2 / 3 :=
      activationProbability_le_sq_div_three _
    _ = (t ^ 2 / 3) * (q ^ 2) ^ n := by
      rw [mul_pow, hpow]
      ring

/-- Activation probabilities sampled at `q ^ n * t` form a summable series
whenever the geometric ratio has absolute value less than one. -/
theorem summable_activationProbability_pow_mul
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    Summable (fun n : ℕ ↦ activationProbability (q ^ n * t)) := by
  have hq2 : q ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one q).2 hq
  have hmajor : Summable (fun n : ℕ ↦ (t ^ 2 / 3) * (q ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg q) hq2).mul_left (t ^ 2 / 3)
  exact Summable.of_nonneg_of_le
    (fun n ↦ activationProbability_nonneg (q ^ n * t))
    (fun n ↦ activationProbability_pow_mul_le q t n)
    hmajor

/-- The activation sum is bounded by the exact sum of its quadratic
geometric majorant. -/
theorem tsum_activationProbability_pow_mul_le
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    (∑' n : ℕ, activationProbability (q ^ n * t)) ≤
      (t ^ 2 / 3) * (1 - q ^ 2)⁻¹ := by
  have hq2 : q ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one q).2 hq
  have hterms := summable_activationProbability_pow_mul hq t
  have hmajor : Summable (fun n : ℕ ↦ (t ^ 2 / 3) * (q ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg q) hq2).mul_left (t ^ 2 / 3)
  calc
    (∑' n : ℕ, activationProbability (q ^ n * t)) ≤
        ∑' n : ℕ, (t ^ 2 / 3) * (q ^ 2) ^ n :=
      hterms.tsum_le_tsum
        (fun n ↦ activationProbability_pow_mul_le q t n) hmajor
    _ = (t ^ 2 / 3) * (1 - q ^ 2)⁻¹ := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (sq_nonneg q) hq2]

/-! ## The normalized geometric effective dimension -/

/-- The effective activation dimension for normalized geometric weights
`(1 - q) * q ^ n`.  Outside the summable range `|q| < 1`, this retains only
the ambient totalized-`tsum` meaning. -/
noncomputable def geometricActivationDimension (q t : ℝ) : ℝ :=
  ∑' n : ℕ, activationProbability (q ^ n * ((1 - q) * t))

/-- The defining terms of `geometricActivationDimension` are summable for
`|q| < 1`. -/
theorem summable_geometricActivationDimension_terms
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    Summable (fun n : ℕ ↦
      activationProbability (q ^ n * ((1 - q) * t))) :=
  summable_activationProbability_pow_mul hq ((1 - q) * t)

/-- The geometric activation dimension vanishes at zero. -/
@[simp] theorem geometricActivationDimension_zero (q : ℝ) :
    geometricActivationDimension q 0 = 0 := by
  simp only [geometricActivationDimension, mul_zero,
    activationProbability_zero, tsum_zero]

/-- Every geometric activation dimension is nonnegative. -/
theorem geometricActivationDimension_nonneg (q t : ℝ) :
    0 ≤ geometricActivationDimension q t := by
  unfold geometricActivationDimension
  exact tsum_nonneg fun n ↦
    activationProbability_nonneg (q ^ n * ((1 - q) * t))

/-- The geometric activation dimension is even in its field parameter. -/
theorem geometricActivationDimension_even (q : ℝ) :
    Function.Even (geometricActivationDimension q) := by
  intro t
  unfold geometricActivationDimension
  refine tsum_congr fun n ↦ ?_
  simpa only [mul_neg] using
    activationProbability_even (q ^ n * ((1 - q) * t))

/-- Removing the zeroth geometric coordinate rescales the field by `q`. -/
theorem geometricActivationDimension_refinement
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    geometricActivationDimension q t =
      activationProbability ((1 - q) * t) +
        geometricActivationDimension q (q * t) := by
  unfold geometricActivationDimension
  have hsum := summable_activationProbability_pow_mul hq ((1 - q) * t)
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  congr 1
  refine tsum_congr fun n ↦ ?_
  congr 1
  rw [pow_succ]
  ring

/-- Difference form of the geometric activation refinement. -/
theorem geometricActivationDimension_sub_refinement
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    geometricActivationDimension q t -
        geometricActivationDimension q (q * t) =
      activationProbability ((1 - q) * t) := by
  rw [geometricActivationDimension_refinement hq t]
  ring

/-- The normalized geometric activation dimension inherits the exact
quadratic geometric-series budget. -/
theorem geometricActivationDimension_le_quadratic
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    geometricActivationDimension q t ≤
      ((((1 - q) * t) ^ 2) / 3) * (1 - q ^ 2)⁻¹ := by
  simpa only [geometricActivationDimension] using
    tsum_activationProbability_pow_mul_le hq ((1 - q) * t)

/-- Splitting after `N` coordinates leaves the same geometric dimension at
the rescaled field `q ^ N * t`. -/
theorem geometricActivationDimension_eq_sum_range_add
    {q : ℝ} (hq : |q| < 1) (t : ℝ) (N : ℕ) :
    geometricActivationDimension q t =
      (∑ n ∈ Finset.range N,
        activationProbability (q ^ n * ((1 - q) * t))) +
        geometricActivationDimension q (q ^ N * t) := by
  unfold geometricActivationDimension
  have hsum := summable_activationProbability_pow_mul hq ((1 - q) * t)
  have hsplit := hsum.sum_add_tsum_nat_add N
  calc
    (∑' n : ℕ, activationProbability (q ^ n * ((1 - q) * t))) =
        (∑ n ∈ Finset.range N,
          activationProbability (q ^ n * ((1 - q) * t))) +
          ∑' n : ℕ,
            activationProbability (q ^ (n + N) * ((1 - q) * t)) :=
      hsplit.symm
    _ = (∑ n ∈ Finset.range N,
          activationProbability (q ^ n * ((1 - q) * t))) +
          ∑' n : ℕ,
            activationProbability (q ^ n * ((1 - q) * (q ^ N * t))) := by
      congr 1
      refine tsum_congr fun n ↦ ?_
      congr 1
      rw [pow_add]
      ring

/-! ## The dyadic effective dimension -/

/-- The effective activation dimension for the dyadic Fabius/Rvachev
weights `2 ^ (-(n+1))`. -/
noncomputable def dyadicEffectiveDimension (t : ℝ) : ℝ :=
  geometricActivationDimension (1 / 2) t

/-- The dyadic definition is the activation sum over the report's indexing
`n ↦ 2 ^ (-(n+1))`. -/
theorem dyadicEffectiveDimension_eq_tsum (t : ℝ) :
    dyadicEffectiveDimension t =
      ∑' n : ℕ,
        activationProbability ((1 / 2 : ℝ) ^ (n + 1) * t) := by
  unfold dyadicEffectiveDimension geometricActivationDimension
  refine tsum_congr fun n ↦ ?_
  congr 1
  rw [pow_succ]
  ring

/-- The dyadic effective dimension vanishes at zero. -/
@[simp] theorem dyadicEffectiveDimension_zero :
    dyadicEffectiveDimension 0 = 0 := by
  exact geometricActivationDimension_zero (1 / 2)

/-- The dyadic effective dimension is nonnegative. -/
theorem dyadicEffectiveDimension_nonneg (t : ℝ) :
    0 ≤ dyadicEffectiveDimension t :=
  geometricActivationDimension_nonneg (1 / 2) t

/-- The dyadic effective dimension is an even function. -/
theorem dyadicEffectiveDimension_even :
    Function.Even dyadicEffectiveDimension :=
  geometricActivationDimension_even (1 / 2)

/-- Half-scale form of the dyadic refinement. -/
theorem dyadicEffectiveDimension_half_refinement (t : ℝ) :
    dyadicEffectiveDimension t =
      activationProbability (t / 2) +
        dyadicEffectiveDimension (t / 2) := by
  change geometricActivationDimension (1 / 2) t =
    activationProbability (t / 2) +
      geometricActivationDimension (1 / 2) (t / 2)
  convert geometricActivationDimension_refinement
    (q := (1 / 2 : ℝ)) (by norm_num) t using 1 <;> ring

/-- Doubling the field adds exactly one local activation probability. -/
theorem dyadicEffectiveDimension_two_mul (t : ℝ) :
    dyadicEffectiveDimension (2 * t) =
      activationProbability t + dyadicEffectiveDimension t := by
  change geometricActivationDimension (1 / 2) (2 * t) =
    activationProbability t + geometricActivationDimension (1 / 2) t
  convert geometricActivationDimension_refinement
    (q := (1 / 2 : ℝ)) (by norm_num) (2 * t) using 1 <;> ring

/-- Difference form of the dyadic effective-dimension refinement. -/
theorem dyadicEffectiveDimension_refinement (t : ℝ) :
    dyadicEffectiveDimension (2 * t) - dyadicEffectiveDimension t =
      activationProbability t := by
  rw [dyadicEffectiveDimension_two_mul]
  ring

/-- The dyadic effective dimension is strictly positive exactly away from
the origin. -/
theorem dyadicEffectiveDimension_pos_iff (t : ℝ) :
    0 < dyadicEffectiveDimension t ↔ t ≠ 0 := by
  constructor
  · intro h ht
    subst t
    simpa using h
  · intro ht
    rw [dyadicEffectiveDimension_half_refinement]
    have ht2 : t / 2 ≠ 0 := div_ne_zero ht (by norm_num)
    have hp : 0 < activationProbability (t / 2) :=
      (activationProbability_pos_iff (t / 2)).2 ht2
    have htail : 0 ≤ dyadicEffectiveDimension (t / 2) :=
      dyadicEffectiveDimension_nonneg (t / 2)
    linarith

/-- The dyadic activation dimension has the global quadratic bound
`t ^ 2 / 9`. -/
theorem dyadicEffectiveDimension_le_sq_div_nine (t : ℝ) :
    dyadicEffectiveDimension t ≤ t ^ 2 / 9 := by
  change geometricActivationDimension (1 / 2) t ≤ t ^ 2 / 9
  calc
    geometricActivationDimension (1 / 2) t ≤
        ((((1 - (1 / 2 : ℝ)) * t) ^ 2) / 3) *
          (1 - (1 / 2 : ℝ) ^ 2)⁻¹ :=
      geometricActivationDimension_le_quadratic (by norm_num) t
    _ = t ^ 2 / 9 := by norm_num <;> ring

/-- Splitting the first `N` dyadic coordinates leaves the dyadic dimension
at the field `(1 / 2) ^ N * t`. -/
theorem dyadicEffectiveDimension_eq_sum_range_add (t : ℝ) (N : ℕ) :
    dyadicEffectiveDimension t =
      (∑ n ∈ Finset.range N,
        activationProbability ((1 / 2 : ℝ) ^ (n + 1) * t)) +
        dyadicEffectiveDimension ((1 / 2 : ℝ) ^ N * t) := by
  change geometricActivationDimension (1 / 2) t =
    (∑ n ∈ Finset.range N,
      activationProbability ((1 / 2 : ℝ) ^ (n + 1) * t)) +
      geometricActivationDimension (1 / 2) ((1 / 2 : ℝ) ^ N * t)
  calc
    geometricActivationDimension (1 / 2) t =
        (∑ n ∈ Finset.range N,
          activationProbability
            ((1 / 2 : ℝ) ^ n * ((1 - (1 / 2 : ℝ)) * t))) +
          geometricActivationDimension (1 / 2)
            ((1 / 2 : ℝ) ^ N * t) :=
      geometricActivationDimension_eq_sum_range_add (by norm_num) t N
    _ = (∑ n ∈ Finset.range N,
          activationProbability ((1 / 2 : ℝ) ^ (n + 1) * t)) +
          geometricActivationDimension (1 / 2)
            ((1 / 2 : ℝ) ^ N * t) := by
      congr 1
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      congr 1
      rw [pow_succ]
      ring

/-- The exact quadratic certificate for the dyadic tail after the first `N`
coordinates.  Its right side is `t ^ 2 / (9 * 4 ^ N)`. -/
theorem dyadicEffectiveDimension_tail_le (t : ℝ) (N : ℕ) :
    dyadicEffectiveDimension ((1 / 2 : ℝ) ^ N * t) ≤
      (t ^ 2 / 9) * (1 / 4 : ℝ) ^ N := by
  calc
    dyadicEffectiveDimension ((1 / 2 : ℝ) ^ N * t) ≤
        (((1 / 2 : ℝ) ^ N * t) ^ 2) / 9 :=
      dyadicEffectiveDimension_le_sq_div_nine _
    _ = (t ^ 2 / 9) * (1 / 4 : ℝ) ^ N := by
      have hpow : (((1 / 2 : ℝ) ^ N) ^ 2) =
          (1 / 4 : ℝ) ^ N := by
        calc
          (((1 / 2 : ℝ) ^ N) ^ 2) =
              (1 / 2 : ℝ) ^ (N * 2) :=
            (pow_mul (1 / 2 : ℝ) N 2).symm
          _ = (1 / 2 : ℝ) ^ (2 * N) := by rw [Nat.mul_comm]
          _ = ((1 / 2 : ℝ) ^ 2) ^ N := pow_mul (1 / 2 : ℝ) 2 N
          _ = (1 / 4 : ℝ) ^ N := by norm_num
      rw [mul_pow, hpow]
      ring

end

end Fabius
