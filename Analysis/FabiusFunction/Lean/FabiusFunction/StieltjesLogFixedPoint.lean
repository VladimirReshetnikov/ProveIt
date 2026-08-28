import FabiusFunction.StieltjesMomentLaurent
import FabiusFunction.MeasureRefinement

/-!
# The logarithmic fixed point of the Stieltjes transform

The transform-layer obligation's *logarithmic fixed point*: the
Stieltjes transform of the up-measure satisfies

`∫ (z-x)⁻¹ dμ_up = ∫ log((2z-x+1)/(2z-x-1)) dμ_up`   (`z > 1`),

the real form of `R₁(z) = E log((2z-X+1)/(2z-X-1))`.  The proof is
the refinement equation at work: conditioning on the rescaled tail
and integrating the uniform digit, the Cauchy kernel integrates to a
logarithm,

`∫_{-1/2}^{1/2} (c-u)⁻¹ du = log((c+1/2)/(c-1/2))`   (`c > 1/2`),

and the affine substitution restores the classical display.
-/

set_option autoImplicit false

open MeasureTheory Real Set

namespace Fabius

/-- The uniform digit integrates the Cauchy kernel to a logarithm:
`∫_{-1/2}^{1/2} (c-u)⁻¹ du = log((c+1/2)/(c-1/2))` for `c > 1/2`. -/
theorem integral_inv_sub_uniform_half {c : ℝ} (hc : 2⁻¹ < c) :
    ∫ u, (c - u)⁻¹ ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) =
      Real.log ((c + 2⁻¹) / (c - 2⁻¹)) := by
  have h1 : ∫ u, (c - u)⁻¹
      ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) =
      ∫ u in (-(2⁻¹ : ℝ))..(2⁻¹ : ℝ), (c - u)⁻¹ := by
    rw [intervalIntegral.integral_of_le
      (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h1]
  have hderiv : ∀ u ∈ Set.uIcc (-(2⁻¹ : ℝ)) (2⁻¹ : ℝ),
      HasDerivAt (fun v => -Real.log (c - v)) ((c - u)⁻¹) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹)] at hu
    have hpos : 0 < c - u := by
      have := hu.2
      linarith
    have h2 : HasDerivAt (fun v : ℝ => c - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub c
    have h3 : HasDerivAt (fun v => Real.log (c - v))
        ((-1) / (c - u)) u := h2.log hpos.ne'
    have h4 : HasDerivAt (fun v => -Real.log (c - v))
        (-((-1) / (c - u))) u := h3.neg
    have h5 : -((-1 : ℝ) / (c - u)) = (c - u)⁻¹ := by
      rw [neg_div, neg_neg, one_div]
    rw [h5] at h4
    exact h4
  have hint : IntervalIntegrable (fun u => (c - u)⁻¹) volume
      (-(2⁻¹ : ℝ)) (2⁻¹ : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹)] at hu
    have hpos : c - u ≠ 0 := by
      have := hu.2
      have : 0 < c - u := by linarith
      exact this.ne'
    exact ((continuousAt_const.sub continuousAt_id).inv₀
      hpos).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show c - -(2⁻¹ : ℝ) = c + 2⁻¹ from by ring,
    Real.log_div (by linarith) (by linarith)]
  ring

/-- **The logarithmic fixed point** (real form): conditioning on the
refinement tail and integrating the uniform digit,
`∫ (z-x)⁻¹ dμ_up = ∫ log((2z-x+1)/(2z-x-1)) dμ_up` for `z > 1`. -/
theorem integral_inv_sub_eq_integral_log (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < z) :
    ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F) =
      ∫ x, Real.log ((2 * z - x + 1) / (2 * z - x - 1))
        ∂(rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  haveI := isProbability_uniform_half
  haveI : IsProbabilityMeasure ((rvachevMeasure F).map (2⁻¹ * ·)) :=
    Measure.isProbabilityMeasure_map
      (measurable_const_mul _).aemeasurable
  have habs : (1 : ℝ) < |z| := by
    rw [abs_of_pos (by linarith)]
    exact hz
  have href : rvachevMeasure F =
      ((rvachevMeasure F).map (2⁻¹ * ·)) ∗
        (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) := by
    rw [rvachevMeasure_refinement F hF]
    exact MeasureTheory.Measure.conv_comm _ _
  have hint : Integrable (fun x => (z - x)⁻¹)
      ((((rvachevMeasure F).map (2⁻¹ * ·)) ∗
        (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) : Measure ℝ)) := by
    rw [← href]
    exact integrable_inv_sub_rvachevMeasure F hF habs
  calc ∫ x, (z - x)⁻¹ ∂(rvachevMeasure F)
      = ∫ x, (z - x)⁻¹ ∂((((rvachevMeasure F).map (2⁻¹ * ·)) ∗
          (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) : Measure ℝ)) := by
        rw [← href]
    _ = ∫ x, ∫ u, (z - (x + u))⁻¹
          ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ∂((rvachevMeasure F).map (2⁻¹ * ·)) :=
        by exact MeasureTheory.integral_conv hint
    _ = ∫ x, Real.log ((z - x + 2⁻¹) / (z - x - 2⁻¹))
          ∂((rvachevMeasure F).map (2⁻¹ * ·)) := by
        refine integral_congr_ae ?_
        have hae : ∀ᵐ x ∂((rvachevMeasure F).map (2⁻¹ * ·)),
            x ∈ Ioo (-(2⁻¹ : ℝ)) 2⁻¹ := by
          refine (MeasureTheory.ae_map_iff
            (measurable_const_mul _).aemeasurable measurableSet_Ioo).mpr
            ?_
          filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x' hx'
          exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
        filter_upwards [hae] with x hx
        have hc : 2⁻¹ < z - x := by
          have := hx.2
          linarith
        have hin : ∀ u : ℝ, (z - (x + u))⁻¹ = ((z - x) - u)⁻¹ :=
          fun u => by
            congr 1
            ring
        simp_rw [hin]
        exact integral_inv_sub_uniform_half hc
    _ = ∫ x', Real.log ((z - 2⁻¹ * x' + 2⁻¹) / (z - 2⁻¹ * x' - 2⁻¹))
          ∂(rvachevMeasure F) := by
        have hmeas : Measurable fun x : ℝ =>
            Real.log ((z - x + 2⁻¹) / (z - x - 2⁻¹)) :=
          (((measurable_const.sub measurable_id).add
            measurable_const).div
            ((measurable_const.sub measurable_id).sub
              measurable_const)).log
        rw [MeasureTheory.integral_map
          (measurable_const_mul _).aemeasurable
          hmeas.aestronglyMeasurable]
    _ = ∫ x, Real.log ((2 * z - x + 1) / (2 * z - x - 1))
          ∂(rvachevMeasure F) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
        congr 1
        have hpos1 : 0 < z - 2⁻¹ * x - 2⁻¹ := by
          linarith [hx.2]
        have hpos2 : 0 < 2 * z - x - 1 := by
          linarith [hx.2]
        rw [div_eq_div_iff hpos1.ne' hpos2.ne']
        ring

end Fabius
