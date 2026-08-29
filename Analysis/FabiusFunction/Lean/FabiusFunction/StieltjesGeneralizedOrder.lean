import FabiusFunction.RefinementConditioning

/-!
# The generalized-order resolvent layer

The transform layer's generalized-order item in real form: the
fractional resolvents `R_α(z) = ∫ (z-x)^{-α} dμ_up` satisfy the same
dyadic hierarchy as the integer powers,

`R_α(z) = (2^{α-1}/(α-1))·(R_{α-1}(2z-1) - R_{α-1}(2z+1))`

for every real `α > 1` and `z > 1` — one conditioning on the
refinement, with the digit-level kernel integral

`∫_{-1/2}^{1/2} (c-u)^{-α} du
  = ((c-1/2)^{1-α} - (c+1/2)^{1-α})/(α-1)`.

The integer hierarchy of `StieltjesResolventHierarchy` is the
specialization `α = n+1`.
-/

set_option autoImplicit false

open MeasureTheory Real Set

namespace Fabius

/-- Off the support the fractional resolvent kernels are
integrable. -/
theorem integrable_rpow_inv_sub_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < z) {α : ℝ} (hα : 0 ≤ α) :
    Integrable (fun x => (z - x) ^ (-α)) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Integrable.mono' (integrable_const ((z - 1) ^ (-α)))
    (((measurable_const.sub measurable_id).pow
      measurable_const).aestronglyMeasurable) ?_
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
  have h1 : (0 : ℝ) < z - 1 := by linarith
  have h2 : z - 1 ≤ z - x := by linarith [hx.2]
  rw [Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
    Real.rpow_neg (by linarith : (0:ℝ) ≤ z - x),
    Real.rpow_neg h1.le, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos h1 α)
    (Real.rpow_le_rpow h1.le h2 hα)

/-- The uniform digit integrates the fractional Cauchy kernel:
`∫_{-1/2}^{1/2} (c-u)^{-α} du
  = ((c-1/2)^{1-α} - (c+1/2)^{1-α})/(α-1)` for `c > 1/2`, `α > 1`. -/
theorem integral_rpow_inv_sub_uniform_half {c α : ℝ} (hc : 2⁻¹ < c)
    (hα : 1 < α) :
    ∫ u, (c - u) ^ (-α)
      ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) =
      ((c - 2⁻¹) ^ (1 - α) - (c + 2⁻¹) ^ (1 - α)) / (α - 1) := by
  have hα0 : α - 1 ≠ 0 := by linarith
  have h1 : ∫ u, (c - u) ^ (-α)
      ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) =
      ∫ u in (-(2⁻¹ : ℝ))..(2⁻¹ : ℝ), (c - u) ^ (-α) := by
    rw [intervalIntegral.integral_of_le
      (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h1]
  have hderiv : ∀ u ∈ Set.uIcc (-(2⁻¹ : ℝ)) (2⁻¹ : ℝ),
      HasDerivAt (fun v => (c - v) ^ (1 - α))
        ((α - 1) * (c - u) ^ (-α)) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹)] at hu
    have hpos : 0 < c - u := by
      have := hu.2
      linarith
    have h2 : HasDerivAt (fun v : ℝ => c - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub c
    have h3 : HasDerivAt (fun y : ℝ => y ^ (1 - α))
        ((1 - α) * (c - u) ^ (1 - α - 1)) (c - u) :=
      Real.hasDerivAt_rpow_const (Or.inl hpos.ne')
    have h5 : HasDerivAt (fun v => (c - v) ^ (1 - α))
        ((1 - α) * (c - u) ^ (1 - α - 1) * (-1)) u := h3.comp u h2
    have hval : (1 - α) * (c - u) ^ (1 - α - 1) * (-1) =
        (α - 1) * (c - u) ^ (-α) := by
      rw [show (1 - α - 1 : ℝ) = -α from by ring]
      ring
    rw [hval] at h5
    exact h5
  have hint : IntervalIntegrable
      (fun u => (α - 1) * (c - u) ^ (-α)) volume
      (-(2⁻¹ : ℝ)) (2⁻¹ : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹)] at hu
    have hpos : 0 < c - u := by
      have := hu.2
      linarith
    exact (continuousAt_const.mul
      ((Real.continuousAt_rpow_const _ _
        (Or.inl hpos.ne')).comp
        (continuousAt_const.sub continuousAt_id))).continuousWithinAt
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  have hend : (c - -(2⁻¹ : ℝ)) ^ (1 - α) = (c + 2⁻¹) ^ (1 - α) := by
    rw [show c - -(2⁻¹ : ℝ) = c + 2⁻¹ from by ring]
  rw [hend] at hftc
  rw [eq_div_iff hα0]
  linear_combination hftc

/-- **The generalized-order hierarchy**: for real `α > 1` and `z > 1`,
`∫ (z-x)^{-α} dμ_up = (2^{α-1}/(α-1))·
  (∫ ((2z-1)-x)^{-(α-1)} dμ_up - ∫ ((2z+1)-x)^{-(α-1)} dμ_up)`. -/
theorem integral_rpow_inv_sub_hierarchy (F : BoundedFabius)
    (hF : IsFabius F) {z α : ℝ} (hz : 1 < z) (hα : 1 < α) :
    ∫ x, (z - x) ^ (-α) ∂(rvachevMeasure F) =
      (2 ^ (α - 1) / (α - 1)) *
        ((∫ x, ((2 * z - 1) - x) ^ (-(α - 1)) ∂(rvachevMeasure F)) -
          ∫ x, ((2 * z + 1) - x) ^ (-(α - 1))
            ∂(rvachevMeasure F)) := by
  haveI := rvachevMeasure_isProbability F hF
  have hintA : Integrable
      (fun x => ((2 * z - 1) - x) ^ (-(α - 1))) (rvachevMeasure F) :=
    integrable_rpow_inv_sub_rvachevMeasure F hF (by linarith)
      (by linarith)
  have hintB : Integrable
      (fun x => ((2 * z + 1) - x) ^ (-(α - 1))) (rvachevMeasure F) :=
    integrable_rpow_inv_sub_rvachevMeasure F hF (by linarith)
      (by linarith)
  have hmeas : Measurable fun x : ℝ =>
      (((z - x) - 2⁻¹) ^ (1 - α) - ((z - x) + 2⁻¹) ^ (1 - α)) /
        (α - 1) :=
    ((((measurable_const.sub measurable_id).sub
      measurable_const).pow measurable_const).sub
      (((measurable_const.sub measurable_id).add
        measurable_const).pow measurable_const)).div_const _
  have hcond := integral_eq_integral_digit_conditioning F hF
    (integrable_rpow_inv_sub_rvachevMeasure F hF hz
      (by linarith : (0:ℝ) ≤ α)) hmeas ?_
  · rw [hcond]
    calc ∫ x', ((z - 2⁻¹ * x' - 2⁻¹) ^ (1 - α) -
            (z - 2⁻¹ * x' + 2⁻¹) ^ (1 - α)) / (α - 1)
          ∂(rvachevMeasure F)
        = ∫ x', (2 ^ (α - 1) / (α - 1)) *
              (((2 * z - 1) - x') ^ (-(α - 1)) -
                ((2 * z + 1) - x') ^ (-(α - 1)))
            ∂(rvachevMeasure F) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x' hx'
          have hA : (0 : ℝ) < (2 * z - 1) - x' := by
            linarith [hx'.2]
          have hB : (0 : ℝ) < (2 * z + 1) - x' := by
            linarith [hx'.2]
          have e1 : z - 2⁻¹ * x' - 2⁻¹ = ((2 * z - 1) - x') / 2 := by
            ring
          have e2 : z - 2⁻¹ * x' + 2⁻¹ = ((2 * z + 1) - x') / 2 := by
            ring
          have hs : ∀ a : ℝ, 0 < a →
              (a / 2) ^ (1 - α) = 2 ^ (α - 1) * a ^ (-(α - 1)) := by
            intro a ha
            rw [Real.div_rpow ha.le (by norm_num : (0:ℝ) ≤ 2),
              division_def,
              ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
              show (-(1 - α) : ℝ) = α - 1 from by ring,
              show (1 - α : ℝ) = -(α - 1) from by ring]
            ring
          rw [e1, e2, hs _ hA, hs _ hB]
          ring
      _ = (2 ^ (α - 1) / (α - 1)) *
            ((∫ x, ((2 * z - 1) - x) ^ (-(α - 1))
              ∂(rvachevMeasure F)) -
              ∫ x, ((2 * z + 1) - x) ^ (-(α - 1))
                ∂(rvachevMeasure F)) := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_sub hintA hintB]
  · filter_upwards [ae_map_mem_Ioo_half F hF] with x hx
    have hc : 2⁻¹ < z - x := by
      have := hx.2
      linarith
    have hin : ∀ u : ℝ,
        (z - (x + u)) ^ (-α) = ((z - x) - u) ^ (-α) := fun u => by
      congr 1
      ring
    simp_rw [hin]
    exact integral_rpow_inv_sub_uniform_half hc hα

end Fabius
