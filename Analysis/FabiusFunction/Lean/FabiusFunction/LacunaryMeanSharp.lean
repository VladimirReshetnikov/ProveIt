import FabiusFunction.LogProductMoments
import FabiusFunction.SincMeanBracket
import FabiusFunction.LacunaryRieszIntegral
import FabiusFunction.GelfondLogisticBound

/-!
# The sharp `2^{-n/2}` bound for the lacunary `L¹` mean

`SincMeanBracket` bounds the mean of the lacunary sine product by
`(√3/2)ⁿ ≈ 0.866ⁿ`, inherited from the pointwise Gelfond bound.  The
`L²` route is sharper and costs nothing extra: Cauchy–Schwarz on the
unit interval against the *exact* second moment

`∫₀¹ ∏_{j<n} sin²(π2ʲt) dt = 2⁻ⁿ`  (`integral_prod_sin_sq_two_pow`)

gives

`I₁(n) = ∫₀¹ ∏_{j<n} |sin(π2ʲt)| dt ≤ 2^{-n/2} = (√2/2)ⁿ ≈ 0.7071ⁿ`.

The Cauchy–Schwarz step is `sq_integral_abs_le` from
`LogProductMoments`, proved there by expanding `∫(|f| − c)² ≥ 0`, so
no `L²`-space machinery is involved anywhere in this file.

* `integral_prod_abs_sin_two_pow_le_sqrt_two` — **the sharp bound**.
* `integral_prod_abs_sin_two_pow_le_sqrt_two'` — in the `range (n+1)`
  indexing of `SincMeanBracket`, for direct comparison.
-/

set_option autoImplicit false

open Finset Real MeasureTheory

namespace Fabius

/-- **The sharp `L¹` mean bound**: `I₁(n) ≤ (√2/2)ⁿ`. -/
theorem integral_prod_abs_sin_two_pow_le_sqrt_two (n : ℕ) :
    ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| ≤
      (Real.sqrt 2 / 2) ^ n := by
  set f : ℝ → ℝ := fun t => ∏ j ∈ range n, Real.sin (π * 2 ^ j * t)
    with hf
  have hcont : Continuous f := by
    rw [hf]
    exact continuous_finsetProd _ (fun j _ => by fun_prop)
  have hint : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable _ _
  have hintsq : IntervalIntegrable (fun t => f t ^ 2)
      MeasureTheory.volume 0 1 :=
    (hcont.pow 2).intervalIntegrable _ _
  -- Cauchy–Schwarz against the exact second moment
  have hCS := sq_integral_abs_le hint hintsq
  have habs : (∫ t in (0:ℝ)..1, |f t|) =
      ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hf]
    exact Finset.abs_prod _ _
  have hsq : (∫ t in (0:ℝ)..1, f t ^ 2) = (1 / 2 : ℝ) ^ n := by
    have hpt : ∀ t : ℝ, f t ^ 2 =
        ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 := by
      intro t
      rw [hf]
      exact (Finset.prod_pow _ _ _).symm
    rw [intervalIntegral.integral_congr (g := fun t =>
      ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2)
      (fun t _ => hpt t)]
    exact integral_prod_sin_sq_two_pow n
  rw [habs, hsq] at hCS
  -- take square roots
  have hI0 : 0 ≤ ∫ t in (0:ℝ)..1,
      ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun u _ => Finset.prod_nonneg (fun j _ => abs_nonneg _))
  have hroot := Real.sqrt_le_sqrt hCS
  rw [Real.sqrt_sq hI0] at hroot
  have hval : Real.sqrt ((1/2 : ℝ) ^ n) = (Real.sqrt 2 / 2) ^ n := by
    have hnn : (0:ℝ) ≤ (Real.sqrt 2 / 2) ^ n := by positivity
    have hsq : ((Real.sqrt 2 / 2) ^ n) ^ 2 = (1/2 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, div_pow,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [← hsq, Real.sqrt_sq hnn]
  rwa [hval] at hroot

/-- The same bound in the `range (n+1)` indexing of
`integral_prod_abs_sin_two_pow_le`, exhibiting it as a sharpening of
that `(√3/2)ⁿ` bracket. -/
theorem integral_prod_abs_sin_two_pow_le_sqrt_two' (n : ℕ) :
    ∫ t in (0:ℝ)..1, ∏ j ∈ range (n + 1), |Real.sin (π * 2 ^ j * t)| ≤
      (Real.sqrt 2 / 2) ^ (n + 1) :=
  integral_prod_abs_sin_two_pow_le_sqrt_two (n + 1)

end Fabius
