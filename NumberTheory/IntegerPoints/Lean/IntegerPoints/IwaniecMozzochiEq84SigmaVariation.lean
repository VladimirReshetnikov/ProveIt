import IntegerPoints.IwaniecMozzochiEq84WeightSteps
import Mathlib.Tactic

/-!
# The smooth-weight contribution to the variation in (8.4)

This module instantiates the compact bounds and scaled mean-value estimate for

`u n = (sigma (n / N) : Complex)`

on the inclusive index interval `0, ..., floor (8N)`.  The first-difference
sum consequently runs over `range (floor (8N))`, so every summand uses a pair
`i, i + 1` whose upper endpoint is still at most `floor (8N)`.

The resulting bounds retain the exact fixed-weight constants `S₀` and `S₁`.
No normalization of `sigma` is assumed.  A final generic corollary plugs this
factor into the product-variation inequality while deliberately leaving the
second complex factor completely abstract.
-/

open Real Set
open scoped BigOperators

namespace LeanProofs.IntegerPoints

/-- The complex-valued copy of the fixed Section 8 weight at scale `N`. -/
noncomputable def section8SigmaWeight (sigma : ℝ → ℝ) (N : ℝ) (n : ℕ) : ℂ :=
  (sigma ((n : ℝ) / N) : ℂ)

/-! ## Uniform endpoint bounds -/

/-- A compact absolute-value bound for `sigma` controls every complex weight
at an index through the inclusive endpoint `floor (8N)`. -/
theorem section8SigmaWeight_norm_le
    {sigma : ℝ → ℝ} {S₀ : ℝ}
    (hsigmaBound : ∀ t ∈ Set.Icc (0 : ℝ) 8, |sigma t| ≤ S₀)
    {N : ℝ} (hN : 0 < N) {i : ℕ} (hi : i ≤ ⌊8 * N⌋₊) :
    ‖section8SigmaWeight sigma N i‖ ≤ S₀ := by
  unfold section8SigmaWeight
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hsigmaBound ((i : ℝ) / N) (section8_scaled_nat_mem_Icc hN hi)

/-! ## The aggregate first-difference bound -/

/-- Summing the scaled mean-value estimate over all consecutive pairs gives
the exact finite bound `floor (8N) * S₁ / N`. -/
theorem section8SigmaWeight_difference_sum_le
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₁ : ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    {N : ℝ} (hN : 0 < N) :
    (∑ i ∈ Finset.range ⌊8 * N⌋₊,
        ‖section8SigmaWeight sigma N i - section8SigmaWeight sigma N (i + 1)‖) ≤
      (⌊8 * N⌋₊ : ℝ) * S₁ / N := by
  calc
    (∑ i ∈ Finset.range ⌊8 * N⌋₊,
        ‖section8SigmaWeight sigma N i - section8SigmaWeight sigma N (i + 1)‖) ≤
        ∑ _i ∈ Finset.range ⌊8 * N⌋₊, S₁ / N := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hiLt : i < ⌊8 * N⌋₊ := Finset.mem_range.mp hi
      have hiSucc : i + 1 ≤ ⌊8 * N⌋₊ := Nat.add_one_le_iff.mpr hiLt
      rw [norm_sub_rev]
      simpa only [section8SigmaWeight] using
        section8_smoothWeight_complex_step_le hsigma hderiv hN hiSucc
    _ = (⌊8 * N⌋₊ : ℝ) * (S₁ / N) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (⌊8 * N⌋₊ : ℝ) * S₁ / N := by ring

/-- The cast of the natural floor is at most its defining real endpoint. -/
theorem section8_floor_cast_le_eight_mul
    {N : ℝ} (hN : 0 ≤ N) :
    (⌊8 * N⌋₊ : ℝ) ≤ 8 * N :=
  Nat.floor_le (mul_nonneg (by norm_num) hN)

/-- Because `S₁` is nonnegative and `N` is positive, the exact floor bound
simplifies safely to the scale-independent bound `8 * S₁`. -/
theorem section8_floor_mul_deriv_div_le
    {N S₁ : ℝ} (hN : 0 < N) (hS₁ : 0 ≤ S₁) :
    (⌊8 * N⌋₊ : ℝ) * S₁ / N ≤ 8 * S₁ := by
  have hfloor : (⌊8 * N⌋₊ : ℝ) ≤ 8 * N :=
    section8_floor_cast_le_eight_mul hN.le
  have hquotient : 0 ≤ S₁ / N := div_nonneg hS₁ hN.le
  calc
    (⌊8 * N⌋₊ : ℝ) * S₁ / N = (⌊8 * N⌋₊ : ℝ) * (S₁ / N) := by ring
    _ ≤ (8 * N) * (S₁ / N) := mul_le_mul_of_nonneg_right hfloor hquotient
    _ = 8 * S₁ := by
      field_simp [hN.ne']

/-- Scale-independent form of the aggregate first-difference estimate. -/
theorem section8SigmaWeight_difference_sum_le_eight
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₁ : ℝ}
    (hS₁ : 0 ≤ S₁)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    {N : ℝ} (hN : 0 < N) :
    (∑ i ∈ Finset.range ⌊8 * N⌋₊,
        ‖section8SigmaWeight sigma N i - section8SigmaWeight sigma N (i + 1)‖) ≤
      8 * S₁ := by
  exact (section8SigmaWeight_difference_sum_le hsigma hderiv hN).trans
    (section8_floor_mul_deriv_div_le hN hS₁)

/-! ## Ready interface for a future second factor -/

/-- The product-variation inequality with its first factor specialized to the
Section 8 smooth weight.  The second factor `v` remains arbitrary; its uniform
norm and first-difference sum are the exact remaining finite obligations. -/
theorem section8SigmaWeight_product_variation_le
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₀ S₁ : ℝ}
    (hsigmaBound : ∀ t ∈ Set.Icc (0 : ℝ) 8, |sigma t| ≤ S₀)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    {N : ℝ} (hN : 0 < N) (v : ℕ → ℂ) (V : ℝ)
    (hv : ∀ i, i ≤ ⌊8 * N⌋₊ → ‖v i‖ ≤ V) :
    FiniteComplexAbel.variation
        (fun i ↦ section8SigmaWeight sigma N i * v i) ⌊8 * N⌋₊ ≤
      S₀ * V + V * ((⌊8 * N⌋₊ : ℝ) * S₁ / N) +
        S₀ * (∑ i ∈ Finset.range ⌊8 * N⌋₊, ‖v i - v (i + 1)‖) := by
  have hu : ∀ i, i ≤ ⌊8 * N⌋₊ → ‖section8SigmaWeight sigma N i‖ ≤ S₀ :=
    fun _i hi ↦ section8SigmaWeight_norm_le hsigmaBound hN hi
  have hdu :
      (∑ i ∈ Finset.range ⌊8 * N⌋₊,
        ‖section8SigmaWeight sigma N i - section8SigmaWeight sigma N (i + 1)‖) ≤
      (⌊8 * N⌋₊ : ℝ) * S₁ / N :=
    section8SigmaWeight_difference_sum_le hsigma hderiv hN
  exact FiniteComplexAbel.variation_mul_le_of_uniform_norm_and_difference_sum_bounds
    (section8SigmaWeight sigma N) v ⌊8 * N⌋₊ S₀ V
      ((⌊8 * N⌋₊ : ℝ) * S₁ / N)
      (∑ i ∈ Finset.range ⌊8 * N⌋₊, ‖v i - v (i + 1)‖)
      hu hv hdu le_rfl

/-! ## Constants depending only on the fixed smooth weight -/

/-- One pair of nonnegative compact constants controls the endpoint norms and
both the exact and simplified first-difference sums for every positive scale. -/
theorem exists_section8SigmaWeight_uniform_and_difference_bounds
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) :
    ∃ S₀ S₁ : ℝ, 0 ≤ S₀ ∧ 0 ≤ S₁ ∧ ∀ N : ℝ, 0 < N →
      (∀ i : ℕ, i ≤ ⌊8 * N⌋₊ → ‖section8SigmaWeight sigma N i‖ ≤ S₀) ∧
      (∑ i ∈ Finset.range ⌊8 * N⌋₊,
          ‖section8SigmaWeight sigma N i - section8SigmaWeight sigma N (i + 1)‖) ≤
        (⌊8 * N⌋₊ : ℝ) * S₁ / N ∧
      (∑ i ∈ Finset.range ⌊8 * N⌋₊,
          ‖section8SigmaWeight sigma N i - section8SigmaWeight sigma N (i + 1)‖) ≤
        8 * S₁ := by
  obtain ⟨S₀, S₁, hS₀, hS₁, hbounds⟩ :=
    exists_section8_smoothWeight_abs_deriv_bounds hsigma
  refine ⟨S₀, S₁, hS₀, hS₁, ?_⟩
  intro N hN
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact section8SigmaWeight_norm_le (fun t ht ↦ (hbounds t ht).1) hN hi
  · exact section8SigmaWeight_difference_sum_le hsigma
      (fun t ht ↦ (hbounds t ht).2) hN
  · exact section8SigmaWeight_difference_sum_le_eight hsigma hS₁
      (fun t ht ↦ (hbounds t ht).2) hN

end LeanProofs.IntegerPoints
