import FabiusFunction.FabiusComputability
import FabiusFunction.FabiusDiscreteLimitIntegration
import FabiusFunction.FiniteAffineCombinationBounds

/-!
# Quantitative rates for the Fabius discrete q-limit

The discrete q-binomial approximant is an exact Toeplitz row of complex-shift
splines,

`D n q x = sum j, omega n j * S (2 * n - j) q x`.

The companion module `FabiusDiscreteLimitToeplitz` packages the whole row in
one q-Pochhammer polynomial.  In particular, its `2 ^ j`-weighted variation is
the explicit rational number `discreteLimitWeightedVariation n`.  This module
combines that finite algebra with the two sharp spline estimates:

* the centered spline has global error at most `2 ^ (-p)`;
* translating its complex parameter from `1 / 2` costs at most
  `2 ^ (-(p-1)) * (exp ‖q - 1/2‖ - 1)`.

Since every degree in row `n` is `2 * n - j`, the elementary identity

`(1 / 2) ^ (2 * n - j) = (1 / 4) ^ n * 2 ^ j`

turns the exact weighted variation into a uniform `4 ^ (-n)` rate.  The main
theorems retain the exact finite q-Pochhammer constant; companion corollaries
use its uniform bound by `64`.  A two-shift theorem also quantifies the finite
translation dependence that disappears in the limit.

## Main results

* `norm_fabiusComplexShiftSpline_sub_extendedFabius_le` combines the centered
  approximation and translation errors for every characterized bounded
  Fabius function.
* `norm_discreteLimitWeightIn_sum_sub_le` is the reusable quantitative
  Toeplitz-row engine for geometrically decaying errors.
* `norm_discreteLimitWeightIn_sum_sub_sum_le` compares two such rows directly,
  without inserting an artificial zero limit or using the mass-one identity.
* `norm_fabiusDiscreteLimitApproximationComplex_sub_globalFabius_le` gives the
  exact q-Pochhammer-weighted `4 ^ (-n)` error.
* `norm_fabiusDiscreteLimitApproximationComplex_center_sub_globalFabius_le`
  is its centered specialization.
* `norm_fabiusDiscreteLimitApproximationComplex_sub_le` and
  `norm_fabiusDiscreteLimitApproximationComplex_sub_center_le` quantify the
  difference between finite rows with different complex translations.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Finset

namespace Fabius

noncomputable section

private theorem half_pow_pred_eq_two_mul (p : ℕ) (hp : 1 ≤ p) :
    (1 / 2 : ℝ) ^ (p - 1) = 2 * (1 / 2 : ℝ) ^ p := by
  rw [pow_sub₀ _ (by norm_num) hp]
  norm_num
  ring

private theorem half_pow_two_mul_sub_eq
    {n j : ℕ} (hj : j ≤ n) :
    (1 / 2 : ℝ) ^ (2 * n - j) =
      (1 / 4 : ℝ) ^ n * (2 : ℝ) ^ j := by
  have hj' : j ≤ 2 * n := by omega
  rw [pow_sub₀ _ (by norm_num) hj', pow_mul, ← inv_pow]
  norm_num

private theorem complexShiftErrorFactor_center :
    2 * Real.exp ‖(1 / 2 : ℂ) - (1 / 2 : ℂ)‖ - 1 = 1 := by
  norm_num

/-! ## One-spline estimates -/

/-- A complex-shift spline approximates the signed extension of every
characterized bounded Fabius function at the explicit geometric rate

`2 ^ (-p) * (2 * exp ‖q - 1/2‖ - 1)`.

The two summands in the constant have different origins: the centered spline
contributes `1`, while translating it contributes
`2 * (exp ‖q - 1/2‖ - 1)`. -/
theorem norm_fabiusComplexShiftSpline_sub_extendedFabius_le
    (F : BoundedFabius) (hF : IsFabius F)
    (p : ℕ) (hp : 1 ≤ p) (q : ℂ) (x : ℝ) :
    ‖fabiusComplexShiftSpline p q x - (extendedFabius F x : ℂ)‖ ≤
      (1 / 2 : ℝ) ^ p *
        (2 * Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) := by
  have hshift :=
    norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp_sub_one_all
      p q x
  have hcenter :
      ‖fabiusComplexShiftSpline p (1 / 2 : ℂ) x -
          (extendedFabius F x : ℂ)‖ ≤
        (1 / 2 : ℝ) ^ p := by
    rw [fabiusComplexShiftSpline_center_eq_uniformSpline]
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      one_div, inv_pow] using
      abs_fabiusUniformSpline_sub_extendedFabius_le F hF p x
  calc
    ‖fabiusComplexShiftSpline p q x - (extendedFabius F x : ℂ)‖ ≤
        ‖fabiusComplexShiftSpline p q x -
            fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ +
          ‖fabiusComplexShiftSpline p (1 / 2 : ℂ) x -
            (extendedFabius F x : ℂ)‖ :=
      by simpa only [dist_eq_norm] using
        dist_triangle
          (fabiusComplexShiftSpline p q x)
          (fabiusComplexShiftSpline p (1 / 2 : ℂ) x)
          (extendedFabius F x : ℂ)
    _ ≤ (1 / 2 : ℝ) ^ (p - 1) *
          (Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) +
        (1 / 2 : ℝ) ^ p := add_le_add hshift hcenter
    _ = (1 / 2 : ℝ) ^ p *
        (2 * Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) := by
      rw [half_pow_pred_eq_two_mul p hp]
      ring

/-- Canonical specialization of
`norm_fabiusComplexShiftSpline_sub_extendedFabius_le` to `globalFabius`. -/
theorem norm_fabiusComplexShiftSpline_sub_globalFabius_le
    (p : ℕ) (hp : 1 ≤ p) (q : ℂ) (x : ℝ) :
    ‖fabiusComplexShiftSpline p q x - (globalFabius x : ℂ)‖ ≤
      (1 / 2 : ℝ) ^ p *
        (2 * Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) := by
  simpa only [globalFabius] using
    norm_fabiusComplexShiftSpline_sub_extendedFabius_le
      fabius fabius_spec p hp q x

/-! ## A quantitative Toeplitz engine -/

/-- A finite Toeplitz row preserves any `2 ^ (-p)` error bound with the exact
loss `discreteLimitWeightedVariation n * 4 ^ (-n)`.  This is the quantitative
counterpart of `tendsto_discreteLimitWeightIn_sum`: no limiting argument is
used, and the conclusion holds at each positive row depth. -/
theorem norm_discreteLimitWeightIn_sum_sub_le
    {K : Type*} [RCLike K] {H : ℕ → K} {L : K} {C : ℝ}
    (hH : ∀ p, 1 ≤ p → ‖H p - L‖ ≤ C * (1 / 2 : ℝ) ^ p)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖(∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * H (2 * n - j)) - L‖ ≤
      (discreteLimitWeightedVariation n : ℝ) * C *
        (1 / 4 : ℝ) ^ n := by
  calc
    ‖(∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * H (2 * n - j)) - L‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖discreteLimitWeightIn K n j‖ *
            (C * (1 / 2 : ℝ) ^ (2 * n - j)) := by
      simpa only [smul_eq_mul] using
        norm_sum_smul_sub_le_of_norm_sub_le
          (Finset.range (n + 1))
          (discreteLimitWeightIn K n)
          (fun j => H (2 * n - j)) L
          (fun j => C * (1 / 2 : ℝ) ^ (2 * n - j))
          (sum_range_discreteLimitWeightIn K n)
          (fun j hj => hH (2 * n - j)
            (hn.trans (discreteLimit_index_ge hj)))
    _ = ∑ j ∈ Finset.range (n + 1),
          ‖discreteLimitWeightIn K n j‖ *
            (C * ((1 / 4 : ℝ) ^ n * (2 : ℝ) ^ j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [half_pow_two_mul_sub_eq
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    _ = ∑ j ∈ Finset.range (n + 1),
          (‖discreteLimitWeightIn K n j‖ * (2 : ℝ) ^ j) *
            (C * (1 / 4 : ℝ) ^ n) := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (∑ j ∈ Finset.range (n + 1),
          ‖discreteLimitWeightIn K n j‖ * (2 : ℝ) ^ j) *
            (C * (1 / 4 : ℝ) ^ n) := by
      rw [Finset.sum_mul]
    _ = (discreteLimitWeightedVariation n : ℝ) * C *
        (1 / 4 : ℝ) ^ n := by
      rw [sum_norm_discreteLimitWeightIn_mul_two_pow K n]
      ring

/-- Two finite Toeplitz rows preserve any pointwise `2 ^ (-p)` comparison,
with the same exact weighted-variation loss as the one-limit engine.  Unlike
`norm_discreteLimitWeightIn_sum_sub_le`, this estimate needs no mass-one
hypothesis: the two rows already have identical coefficients. -/
theorem norm_discreteLimitWeightIn_sum_sub_sum_le
    {K : Type*} [RCLike K] {H G : ℕ → K} {C : ℝ}
    (hHG : ∀ p, 1 ≤ p → ‖H p - G p‖ ≤ C * (1 / 2 : ℝ) ^ p)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖(∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * H (2 * n - j)) -
      ∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * G (2 * n - j)‖ ≤
      (discreteLimitWeightedVariation n : ℝ) * C *
        (1 / 4 : ℝ) ^ n := by
  calc
    ‖(∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * H (2 * n - j)) -
      ∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * G (2 * n - j)‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖discreteLimitWeightIn K n j‖ *
            (C * (1 / 2 : ℝ) ^ (2 * n - j)) := by
      simpa only [smul_eq_mul] using
        norm_sum_smul_sub_sum_smul_le_of_norm_sub_le
          (Finset.range (n + 1))
          (discreteLimitWeightIn K n)
          (fun j => H (2 * n - j))
          (fun j => G (2 * n - j))
          (fun j => C * (1 / 2 : ℝ) ^ (2 * n - j))
          (fun j hj => hHG (2 * n - j)
            (hn.trans (discreteLimit_index_ge hj)))
    _ = ∑ j ∈ Finset.range (n + 1),
          ‖discreteLimitWeightIn K n j‖ *
            (C * ((1 / 4 : ℝ) ^ n * (2 : ℝ) ^ j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [half_pow_two_mul_sub_eq
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    _ = ∑ j ∈ Finset.range (n + 1),
          (‖discreteLimitWeightIn K n j‖ * (2 : ℝ) ^ j) *
            (C * (1 / 4 : ℝ) ^ n) := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (∑ j ∈ Finset.range (n + 1),
          ‖discreteLimitWeightIn K n j‖ * (2 : ℝ) ^ j) *
            (C * (1 / 4 : ℝ) ^ n) := by
      rw [Finset.sum_mul]
    _ = (discreteLimitWeightedVariation n : ℝ) * C *
        (1 / 4 : ℝ) ^ n := by
      rw [sum_norm_discreteLimitWeightIn_mul_two_pow K n]
      ring

/-! ## Exact and uniform discrete-row rates -/

/-- Exact finite error for the complex discrete q-limit.  The rational factor
`discreteLimitWeightedVariation n` is the q-Pochhammer quotient
`(-1; 1/2)_n / (1/2; 1/2)_n`; retaining it is sharper than replacing it by
its uniform upper bound `64`. -/
theorem norm_fabiusDiscreteLimitApproximationComplex_sub_globalFabius_le
    (q : ℂ) (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖fabiusDiscreteLimitApproximationComplex q x n -
        (globalFabius x : ℂ)‖ ≤
      (discreteLimitWeightedVariation n : ℝ) *
        (2 * Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) *
        (1 / 4 : ℝ) ^ n := by
  rw [fabiusDiscreteLimitApproximationComplex_eq_weighted_shiftSpline]
  refine norm_discreteLimitWeightIn_sum_sub_le
    (K := ℂ)
    (H := fun p => fabiusComplexShiftSpline p q x)
    (L := (globalFabius x : ℂ))
    (C := 2 * Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) ?_ n hn
  · intro p hp
    simpa only [mul_comm] using
      norm_fabiusComplexShiftSpline_sub_globalFabius_le p hp q x

/-- Uniform version of the complex discrete-row error, with the explicit
q-independent row constant `64`. -/
theorem norm_fabiusDiscreteLimitApproximationComplex_sub_globalFabius_le_sixtyFour
    (q : ℂ) (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖fabiusDiscreteLimitApproximationComplex q x n -
        (globalFabius x : ℂ)‖ ≤
      64 * (2 * Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) *
        (1 / 4 : ℝ) ^ n := by
  refine (norm_fabiusDiscreteLimitApproximationComplex_sub_globalFabius_le
    q x n hn).trans ?_
  have hC : 0 ≤ 2 * Real.exp ‖q - (1 / 2 : ℂ)‖ - 1 := by
    have hexp := Real.one_le_exp (norm_nonneg (q - (1 / 2 : ℂ)))
    linarith
  have hvariation :
      (discreteLimitWeightedVariation n : ℝ) ≤ 64 := by
    exact_mod_cast discreteLimitWeightedVariation_le n
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hvariation hC) (by positivity)

/-- At the centered shift, the exponential constant is exactly one: the
`n`-th discrete row has error at most
`discreteLimitWeightedVariation n * 4 ^ (-n)`. -/
theorem norm_fabiusDiscreteLimitApproximationComplex_center_sub_globalFabius_le
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖fabiusDiscreteLimitApproximationComplex (1 / 2 : ℂ) x n -
        (globalFabius x : ℂ)‖ ≤
      (discreteLimitWeightedVariation n : ℝ) *
        (1 / 4 : ℝ) ^ n := by
  simpa only [complexShiftErrorFactor_center, mul_one] using
    norm_fabiusDiscreteLimitApproximationComplex_sub_globalFabius_le
      (1 / 2 : ℂ) x n hn

/-- Uniform centered-row error with the explicit constant `64`. -/
theorem norm_fabiusDiscreteLimitApproximationComplex_center_sub_globalFabius_le_sixtyFour
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖fabiusDiscreteLimitApproximationComplex (1 / 2 : ℂ) x n -
        (globalFabius x : ℂ)‖ ≤
      64 * (1 / 4 : ℝ) ^ n := by
  simpa only [complexShiftErrorFactor_center, mul_one] using
    norm_fabiusDiscreteLimitApproximationComplex_sub_globalFabius_le_sixtyFour
      (1 / 2 : ℂ) x n hn

/-! ## Quantitative translation independence -/

/-- Two finite discrete rows with arbitrary complex translations differ by at
most the sum of their translation radii about the centered row, with the same
exact `4 ^ (-n)` q-Pochhammer factor. -/
theorem norm_fabiusDiscreteLimitApproximationComplex_sub_le
    (q₁ q₂ : ℂ) (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖fabiusDiscreteLimitApproximationComplex q₁ x n -
        fabiusDiscreteLimitApproximationComplex q₂ x n‖ ≤
      2 * (discreteLimitWeightedVariation n : ℝ) *
        ((Real.exp ‖q₁ - (1 / 2 : ℂ)‖ - 1) +
          (Real.exp ‖q₂ - (1 / 2 : ℂ)‖ - 1)) *
        (1 / 4 : ℝ) ^ n := by
  rw [fabiusDiscreteLimitApproximationComplex_eq_weighted_shiftSpline,
    fabiusDiscreteLimitApproximationComplex_eq_weighted_shiftSpline]
  have hfactor :
      2 * (discreteLimitWeightedVariation n : ℝ) *
          ((Real.exp ‖q₁ - (1 / 2 : ℂ)‖ - 1) +
            (Real.exp ‖q₂ - (1 / 2 : ℂ)‖ - 1)) =
        (discreteLimitWeightedVariation n : ℝ) *
          (2 * ((Real.exp ‖q₁ - (1 / 2 : ℂ)‖ - 1) +
            (Real.exp ‖q₂ - (1 / 2 : ℂ)‖ - 1))) := by
    ring
  rw [hfactor]
  refine norm_discreteLimitWeightIn_sum_sub_sum_le
    (K := ℂ)
    (H := fun p =>
      fabiusComplexShiftSpline p q₁ x)
    (G := fun p =>
      fabiusComplexShiftSpline p q₂ x)
    (C := 2 * ((Real.exp ‖q₁ - (1 / 2 : ℂ)‖ - 1) +
      (Real.exp ‖q₂ - (1 / 2 : ℂ)‖ - 1))) ?_ n hn
  intro p hp
  have htriangle :
      ‖fabiusComplexShiftSpline p q₁ x -
          fabiusComplexShiftSpline p q₂ x‖ ≤
        ‖fabiusComplexShiftSpline p q₁ x -
          fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ +
        ‖fabiusComplexShiftSpline p q₂ x -
          fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ := by
    calc
      ‖fabiusComplexShiftSpline p q₁ x -
          fabiusComplexShiftSpline p q₂ x‖ ≤
          ‖fabiusComplexShiftSpline p q₁ x -
            fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ +
          ‖fabiusComplexShiftSpline p (1 / 2 : ℂ) x -
            fabiusComplexShiftSpline p q₂ x‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle
            (fabiusComplexShiftSpline p q₁ x)
            (fabiusComplexShiftSpline p (1 / 2 : ℂ) x)
            (fabiusComplexShiftSpline p q₂ x)
      _ = ‖fabiusComplexShiftSpline p q₁ x -
            fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ +
          ‖fabiusComplexShiftSpline p q₂ x -
            fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ := by
        rw [norm_sub_rev
          (fabiusComplexShiftSpline p (1 / 2 : ℂ) x)
          (fabiusComplexShiftSpline p q₂ x)]
  refine htriangle.trans ?_
  have h₁ :=
    norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp_sub_one_all
      p q₁ x
  have h₂ :=
    norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp_sub_one_all
      p q₂ x
  calc
    ‖fabiusComplexShiftSpline p q₁ x -
          fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ +
        ‖fabiusComplexShiftSpline p q₂ x -
          fabiusComplexShiftSpline p (1 / 2 : ℂ) x‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) *
          (Real.exp ‖q₁ - (1 / 2 : ℂ)‖ - 1) +
        (1 / 2 : ℝ) ^ (p - 1) *
          (Real.exp ‖q₂ - (1 / 2 : ℂ)‖ - 1) := add_le_add h₁ h₂
    _ = 2 * ((Real.exp ‖q₁ - (1 / 2 : ℂ)‖ - 1) +
          (Real.exp ‖q₂ - (1 / 2 : ℂ)‖ - 1)) *
        (1 / 2 : ℝ) ^ p := by
      rw [half_pow_pred_eq_two_mul p hp]
      ring

/-- Centered specialization of the two-shift theorem.  This is the exact
quantitative form of finite-row translation independence printed in the
research-frontier synthesis. -/
theorem norm_fabiusDiscreteLimitApproximationComplex_sub_center_le
    (q : ℂ) (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖fabiusDiscreteLimitApproximationComplex q x n -
        fabiusDiscreteLimitApproximationComplex (1 / 2 : ℂ) x n‖ ≤
      2 * (discreteLimitWeightedVariation n : ℝ) *
        (Real.exp ‖q - (1 / 2 : ℂ)‖ - 1) *
        (1 / 4 : ℝ) ^ n := by
  simpa using
    norm_fabiusDiscreteLimitApproximationComplex_sub_le
      q (1 / 2 : ℂ) x n hn

end

end Fabius
