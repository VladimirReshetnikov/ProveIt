import IntegerPoints.FiniteComplexProductVariation
import IntegerPoints.IwaniecMozzochiEq84WeightBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Scaled smooth-weight steps for Iwaniec--Mozzochi (8.4)

This module supplies the finite-step input needed when Abel summation is
applied to the Section 8 weight.  If `0 < N` and `n + 1 <= floor (8N)`, then
both scaled endpoints `n / N` and `(n + 1) / N` lie in `[0, 8]`.  The mean
value theorem therefore turns a compact derivative bound for the fixed smooth
weight into the precise step estimate

`|sigma ((n + 1) / N) - sigma (n / N)| <= S₁ / N`.

The imported theory-independent companion `FiniteComplexProductVariation`
keeps the endpoint norms and both first-difference sums visible.  In
particular, this bridge makes no normalization assumption on `sigma` and no
assumption at all about a future phase `t`.
-/

open Real Set

namespace LeanProofs.IntegerPoints

/-! ## The scaled `[0, 8]` window -/

/-- Every natural index below `floor (8N)` scales into `[0, 8]` when `N` is
positive.  The floor-to-real and division conversions are deliberately kept
explicit for downstream endpoint audits. -/
theorem section8_scaled_nat_mem_Icc
    {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n ≤ ⌊8 * N⌋₊) :
    (n : ℝ) / N ∈ Set.Icc (0 : ℝ) 8 := by
  have hnCast : (n : ℝ) ≤ (⌊8 * N⌋₊ : ℝ) := by
    exact_mod_cast hn
  have hfloor : (⌊8 * N⌋₊ : ℝ) ≤ 8 * N :=
    Nat.floor_le (mul_nonneg (by norm_num) hN.le)
  constructor
  · exact div_nonneg (Nat.cast_nonneg n) hN.le
  · exact (div_le_iff₀ hN).2 (hnCast.trans hfloor)

/-- A derivative bound on the full compact support window gives the exact
`S₁ / N` first-difference bound at every admissible pair of consecutive
indices.  Both endpoint memberships in `[0, 8]` are exhibited before the
mean-value theorem is invoked. -/
theorem section8_smoothWeight_step_le
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₁ : ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n + 1 ≤ ⌊8 * N⌋₊) :
    |sigma (((n + 1 : ℕ) : ℝ) / N) - sigma ((n : ℝ) / N)| ≤ S₁ / N := by
  let u : ℝ := (n : ℝ) / N
  let v : ℝ := ((n + 1 : ℕ) : ℝ) / N
  have hnFloor : n ≤ ⌊8 * N⌋₊ := (Nat.le_succ n).trans hn
  have hu : u ∈ Set.Icc (0 : ℝ) 8 := by
    exact section8_scaled_nat_mem_Icc hN hnFloor
  have hv : v ∈ Set.Icc (0 : ℝ) 8 := by
    exact section8_scaled_nat_mem_Icc hN hn
  have hdiff : ∀ z ∈ Set.Icc (0 : ℝ) 8, DifferentiableAt ℝ sigma z := by
    intro z _hz
    exact hsigma.1.differentiable (by simp) z
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (f := sigma) (s := Set.Icc (0 : ℝ) 8)
    (x := u) (y := v) (C := S₁)
    hdiff (fun z hz ↦ by simpa only [Real.norm_eq_abs] using hderiv z hz)
    (convex_Icc (0 : ℝ) 8) hu hv
  have hsub : v - u = 1 / N := by
    dsimp [u, v]
    push_cast
    ring
  have huv : ‖v - u‖ = 1 / N := by
    rw [Real.norm_eq_abs, hsub, abs_of_pos]
    positivity
  change |sigma v - sigma u| ≤ S₁ / N
  simpa [Real.norm_eq_abs, huv, div_eq_mul_inv] using hmvt

/-- The preceding real estimate after the canonical embedding into `ℂ`, in
the form consumed by complex Abel summation. -/
theorem section8_smoothWeight_complex_step_le
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₁ : ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n + 1 ≤ ⌊8 * N⌋₊) :
    ‖(sigma (((n + 1 : ℕ) : ℝ) / N) : ℂ) -
        (sigma ((n : ℝ) / N) : ℂ)‖ ≤ S₁ / N := by
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
    section8_smoothWeight_step_le hsigma hderiv hN hn

/-- A caller can choose one nonnegative derivative constant, depending only on
the fixed smooth weight, which controls every admissible scale and index. -/
theorem exists_section8_smoothWeight_step_bound
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) :
    ∃ S₁ : ℝ, 0 ≤ S₁ ∧ ∀ (N : ℝ) (n : ℕ), 0 < N →
      n + 1 ≤ ⌊8 * N⌋₊ →
      |sigma (((n + 1 : ℕ) : ℝ) / N) - sigma ((n : ℝ) / N)| ≤ S₁ / N := by
  obtain ⟨_S₀, S₁, _hS₀, hS₁, hbounds⟩ :=
    exists_section8_smoothWeight_abs_deriv_bounds hsigma
  refine ⟨S₁, hS₁, ?_⟩
  intro N n hN hn
  exact section8_smoothWeight_step_le hsigma
    (fun t ht ↦ (hbounds t ht).2) hN hn

end LeanProofs.IntegerPoints
