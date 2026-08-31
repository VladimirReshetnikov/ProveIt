import FabiusFunction.ActivationSeries
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
a nonsummable real family is zero.  The hypothesis `|q| < 1` is the uniform,
nondegenerate convergence regime used below; without it no general summability
is promised, although degenerate cases may still converge.  Probability-law
applications normally further assume `0 ≤ q < 1`.  At `q = 1 / 2` this is
exactly the dyadic effective dimension from the Fabius/Rvachev active-digit
law.
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
  calc
    activationProbability (q ^ n * t) ≤ (t ^ 2 / 3) * (q ^ n) ^ 2 :=
      activationProbability_mul_le_quadratic (q ^ n) t
    _ = (t ^ 2 / 3) * (q ^ 2) ^ n := by
      rw [pow_right_comm]

/-- Activation probabilities sampled at `q ^ n * t` form a summable series
whenever the geometric ratio has absolute value less than one. -/
theorem summable_activationProbability_pow_mul
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    Summable (fun n : ℕ ↦ activationProbability (q ^ n * t)) := by
  have hq2 : q ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one q).2 hq
  apply summable_activationProbability_mul_of_summable_sq ?_ t
  simpa only [pow_right_comm] using
    summable_geometric_of_lt_one (sq_nonneg q) hq2

/-- The activation sum is bounded by the exact sum of its quadratic
geometric majorant. -/
theorem tsum_activationProbability_pow_mul_le
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    (∑' n : ℕ, activationProbability (q ^ n * t)) ≤
      (t ^ 2 / 3) * (1 - q ^ 2)⁻¹ := by
  have hq2 : q ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one q).2 hq
  have hw : Summable (fun n : ℕ ↦ (q ^ n) ^ 2) := by
    simpa only [pow_right_comm] using
      summable_geometric_of_lt_one (sq_nonneg q) hq2
  calc
    (∑' n : ℕ, activationProbability (q ^ n * t)) ≤
        (t ^ 2 / 3) * ∑' n : ℕ, (q ^ n) ^ 2 :=
      tsum_activationProbability_mul_le hw t
    _ = (t ^ 2 / 3) * (1 - q ^ 2)⁻¹ := by
      congr 1
      simpa only [pow_right_comm] using
        tsum_geometric_of_lt_one (sq_nonneg q) hq2

/-- The squared normalized geometric weights have total mass
`(1 - q) / (1 + q)` throughout the convergent range. -/
theorem hasSum_normalizedGeometricWeight_sq
    {q : ℝ} (hq : |q| < 1) :
    HasSum (fun n : ℕ ↦ (q ^ n * (1 - q)) ^ 2)
      ((1 - q) / (1 + q)) := by
  have hq2 : q ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one q).2 hq
  rcases abs_lt.mp hq with ⟨hq_neg, hq_pos⟩
  have hminus : 1 - q ≠ 0 := by linarith
  have hplus : 1 + q ≠ 0 := by linarith
  have hsum :
      HasSum (fun n : ℕ ↦ (q ^ n * (1 - q)) ^ 2)
        ((1 - q) ^ 2 * (1 - q ^ 2)⁻¹) := by
    simpa only [mul_pow, pow_right_comm, mul_comm] using
      (hasSum_geometric_of_lt_one (sq_nonneg q) hq2).mul_left
        ((1 - q) ^ 2)
  have hvalue :
      (1 - q) / (1 + q) = (1 - q) ^ 2 * (1 - q ^ 2)⁻¹ := by
    rw [show 1 - q ^ 2 = (1 - q) * (1 + q) by ring]
    field_simp [hminus, hplus]
  rw [hvalue]
  exact hsum

/-! ## The normalized geometric effective dimension -/

/-- The effective activation dimension for normalized geometric weights
`(1 - q) * q ^ n`.  The results below use the uniform convergence regime
`|q| < 1`; outside it this definition retains the ambient totalized-`tsum`
meaning, even though some degenerate parameter choices remain summable. -/
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

/-- At zero geometric ratio, only the zeroth coordinate remains. -/
@[simp] theorem geometricActivationDimension_zero_ratio (t : ℝ) :
    geometricActivationDimension 0 t = activationProbability t := by
  simpa using
    (geometricActivationDimension_refinement
      (q := (0 : ℝ)) (by norm_num) t)

/-- The zeroth geometric coordinate is a lower bound for the full effective
dimension. -/
theorem activationProbability_scale_le_geometricActivationDimension
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    activationProbability ((1 - q) * t) ≤
      geometricActivationDimension q t := by
  rw [geometricActivationDimension_refinement hq t]
  exact le_add_of_nonneg_right
    (geometricActivationDimension_nonneg q (q * t))

/-- In the convergent geometric range, the effective dimension is positive
exactly away from the origin. -/
theorem geometricActivationDimension_pos_iff
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    0 < geometricActivationDimension q t ↔ t ≠ 0 := by
  constructor
  · intro h ht
    subst t
    simp at h
  · intro ht
    have hq_lt : q < 1 := (abs_lt.mp hq).2
    have hscale : (1 - q) * t ≠ 0 :=
      mul_ne_zero
        (sub_ne_zero.mpr (ne_of_gt hq_lt))
        ht
    exact lt_of_lt_of_le
      ((activationProbability_pos_iff ((1 - q) * t)).2 hscale)
      (activationProbability_scale_le_geometricActivationDimension hq t)

/-- The normalized geometric activation dimension inherits the exact
quadratic geometric-series budget. -/
theorem geometricActivationDimension_le_quadratic
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    geometricActivationDimension q t ≤
      ((((1 - q) * t) ^ 2) / 3) * (1 - q ^ 2)⁻¹ := by
  simpa only [geometricActivationDimension] using
    tsum_activationProbability_pow_mul_le hq ((1 - q) * t)

/-- The normalized geometric dimension has the simplified quadratic
coefficient `(1 - q) / (3 * (1 + q))`. -/
theorem geometricActivationDimension_le_normalized_quadratic
    {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    geometricActivationDimension q t ≤
      (1 - q) * t ^ 2 / (3 * (1 + q)) := by
  rcases abs_lt.mp hq with ⟨hq_neg, hq_pos⟩
  have hminus : 1 - q ≠ 0 := by linarith
  have hplus : 1 + q ≠ 0 := by linarith
  calc
    geometricActivationDimension q t ≤
        ((((1 - q) * t) ^ 2) / 3) * (1 - q ^ 2)⁻¹ :=
      geometricActivationDimension_le_quadratic hq t
    _ = (1 - q) * t ^ 2 / (3 * (1 + q)) := by
      rw [show 1 - q ^ 2 = (1 - q) * (1 + q) by ring]
      field_simp [hminus, hplus]

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

/-- After the first `N` coordinates, the remaining geometric dimension has
an explicitly decaying quadratic bound. -/
theorem geometricActivationDimension_tail_le
    {q : ℝ} (hq : |q| < 1) (t : ℝ) (N : ℕ) :
    geometricActivationDimension q (q ^ N * t) ≤
      ((1 - q) * t ^ 2 / (3 * (1 + q))) * (q ^ 2) ^ N := by
  calc
    geometricActivationDimension q (q ^ N * t) ≤
        (1 - q) * (q ^ N * t) ^ 2 / (3 * (1 + q)) :=
      geometricActivationDimension_le_normalized_quadratic
        hq (q ^ N * t)
    _ = ((1 - q) * t ^ 2 / (3 * (1 + q))) *
        (q ^ 2) ^ N := by
      rw [mul_pow, pow_right_comm q N 2]
      ring

/-- Every finite prefix underestimates the full convergent geometric
activation dimension. -/
theorem sum_range_activationProbability_le_geometricActivationDimension
    {q : ℝ} (hq : |q| < 1) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      activationProbability (q ^ n * ((1 - q) * t))) ≤
      geometricActivationDimension q t := by
  calc
    (∑ n ∈ Finset.range N,
        activationProbability (q ^ n * ((1 - q) * t))) ≤
        (∑ n ∈ Finset.range N,
          activationProbability (q ^ n * ((1 - q) * t))) +
          geometricActivationDimension q (q ^ N * t) :=
      le_add_of_nonneg_right
        (geometricActivationDimension_nonneg q (q ^ N * t))
    _ = geometricActivationDimension q t :=
      (geometricActivationDimension_eq_sum_range_add hq t N).symm

/-- A finite prefix plus the explicit quadratic tail bound overestimates the
full geometric activation dimension. -/
theorem geometricActivationDimension_le_sum_range_add_tail
    {q : ℝ} (hq : |q| < 1) (t : ℝ) (N : ℕ) :
    geometricActivationDimension q t ≤
      (∑ n ∈ Finset.range N,
        activationProbability (q ^ n * ((1 - q) * t))) +
      ((1 - q) * t ^ 2 / (3 * (1 + q))) * (q ^ 2) ^ N := by
  rw [geometricActivationDimension_eq_sum_range_add hq t N]
  exact add_le_add_right
    (geometricActivationDimension_tail_le hq t N)
    (∑ n ∈ Finset.range N,
      activationProbability (q ^ n * ((1 - q) * t)))

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
  calc
    geometricActivationDimension (1 / 2) t =
        activationProbability ((1 - (1 / 2 : ℝ)) * t) +
          geometricActivationDimension (1 / 2) ((1 / 2) * t) :=
      geometricActivationDimension_refinement (by norm_num) t
    _ = activationProbability (t / 2) +
        geometricActivationDimension (1 / 2) (t / 2) := by
      congr 2
      all_goals ring

/-- Doubling the field adds exactly one local activation probability. -/
theorem dyadicEffectiveDimension_two_mul (t : ℝ) :
    dyadicEffectiveDimension (2 * t) =
      activationProbability t + dyadicEffectiveDimension t := by
  change geometricActivationDimension (1 / 2) (2 * t) =
    activationProbability t + geometricActivationDimension (1 / 2) t
  calc
    geometricActivationDimension (1 / 2) (2 * t) =
        activationProbability ((1 - (1 / 2 : ℝ)) * (2 * t)) +
          geometricActivationDimension (1 / 2) ((1 / 2) * (2 * t)) :=
      geometricActivationDimension_refinement (by norm_num) (2 * t)
    _ = activationProbability t +
        geometricActivationDimension (1 / 2) t := by
      congr 2
      all_goals ring

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
  change 0 < geometricActivationDimension (1 / 2) t ↔ t ≠ 0
  exact geometricActivationDimension_pos_iff
    (q := (1 / 2 : ℝ)) (by norm_num) t

/-- The dyadic activation dimension has the global quadratic bound
`t ^ 2 / 9`. -/
theorem dyadicEffectiveDimension_le_sq_div_nine (t : ℝ) :
    dyadicEffectiveDimension t ≤ t ^ 2 / 9 := by
  change geometricActivationDimension (1 / 2) t ≤ t ^ 2 / 9
  calc
    geometricActivationDimension (1 / 2) t ≤
        (1 - (1 / 2 : ℝ)) * t ^ 2 /
          (3 * (1 + (1 / 2 : ℝ))) :=
      geometricActivationDimension_le_normalized_quadratic (by norm_num) t
    _ = t ^ 2 / 9 := by ring

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
  change geometricActivationDimension (1 / 2)
      ((1 / 2 : ℝ) ^ N * t) ≤
    (t ^ 2 / 9) * (1 / 4 : ℝ) ^ N
  calc
    geometricActivationDimension (1 / 2) ((1 / 2 : ℝ) ^ N * t) ≤
        ((1 - (1 / 2 : ℝ)) * t ^ 2 /
          (3 * (1 + (1 / 2 : ℝ)))) *
          (((1 / 2 : ℝ) ^ 2) ^ N) :=
      geometricActivationDimension_tail_le (by norm_num) t N
    _ = (t ^ 2 / 9) * (1 / 4 : ℝ) ^ N := by
      have hcoefficient :
          (1 - (1 / 2 : ℝ)) * t ^ 2 /
              (3 * (1 + (1 / 2 : ℝ))) = t ^ 2 / 9 := by
        ring
      have hratio : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
      rw [hcoefficient, hratio]

end

end Fabius
