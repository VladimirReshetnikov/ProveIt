import FabiusFunction.StieltjesLogFixedPoint

/-!
# The resolvent hierarchy of the Stieltjes transform

The differentiated hierarchy of the logarithmic fixed point, obtained
*without* differentiating under the integral: for `R_n(z) = ∫ (z-x)⁻ⁿ dμ_up`,

`R_{n+1}(z) = (2ⁿ/n)·(R_n(2z-1) - R_n(2z+1))`   (`n ≥ 1`, `z > 1`).

The proof is the same conditioning as the fixed point: the uniform
digit integrates the `(n+1)`-st Cauchy kernel exactly,

`∫_{-1/2}^{1/2} (c-u)^{-(n+1)} du = ((c-1/2)⁻ⁿ - (c+1/2)⁻ⁿ)/n`,

and the dyadic rescaling turns the two boundary evaluations into the
two shifted resolvents.

* `integrable_pow_inv_sub_rvachevMeasure` — all resolvent powers are
  integrable off the support;
* `integral_pow_inv_sub_uniform_half` — the digit-level kernel
  integral;
* `integral_pow_inv_sub_succ` — **the hierarchy identity**.
-/

set_option autoImplicit false

open MeasureTheory Real Set

namespace Fabius

/-- All resolvent powers are integrable off the support. -/
theorem integrable_pow_inv_sub_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < |z|) (n : ℕ) :
    Integrable (fun x => ((z - x)⁻¹) ^ n) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Integrable.mono' (integrable_const (((|z| - 1)⁻¹) ^ n))
    (((measurable_const.sub measurable_id).inv.pow_const
      n).aestronglyMeasurable) ?_
  filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
  have hxabs : |x| ≤ 1 := le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
  have hle : |z| - 1 ≤ |z - x| := by
    have h := abs_sub_abs_le_abs_sub z x
    linarith
  rw [norm_pow, norm_inv, Real.norm_eq_abs]
  refine pow_le_pow_left₀ (by positivity) ?_ n
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by linarith) hle

/-- The uniform digit integrates the `(n+1)`-st Cauchy kernel:
`∫_{-1/2}^{1/2} (c-u)^{-(n+1)} du = ((c-1/2)⁻ⁿ - (c+1/2)⁻ⁿ)/n`. -/
theorem integral_pow_inv_sub_uniform_half {c : ℝ} (hc : 2⁻¹ < c)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ u, ((c - u)⁻¹) ^ (n + 1)
      ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) =
      (((c - 2⁻¹)⁻¹) ^ n - ((c + 2⁻¹)⁻¹) ^ n) / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ∫ u, ((c - u)⁻¹) ^ (n + 1)
      ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) =
      ∫ u in (-(2⁻¹ : ℝ))..(2⁻¹ : ℝ), ((c - u)⁻¹) ^ (n + 1) := by
    rw [intervalIntegral.integral_of_le
      (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h1]
  have hderiv : ∀ u ∈ Set.uIcc (-(2⁻¹ : ℝ)) (2⁻¹ : ℝ),
      HasDerivAt (fun v => ((c - v)⁻¹) ^ n)
        ((n : ℝ) * ((c - u)⁻¹) ^ (n + 1)) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹)] at hu
    have hpos : 0 < c - u := by
      have := hu.2
      linarith
    have h2 : HasDerivAt (fun v : ℝ => c - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub c
    have h3 : HasDerivAt (fun v => (c - v)⁻¹)
        (-(-1) / (c - u) ^ 2) u := h2.inv hpos.ne'
    have h4 : HasDerivAt (fun v => ((c - v)⁻¹) ^ n)
        ((n : ℝ) * ((c - u)⁻¹) ^ (n - 1) *
          (-(-1) / (c - u) ^ 2)) u := h3.pow n
    have hval : (n : ℝ) * ((c - u)⁻¹) ^ (n - 1) *
        (-(-1) / (c - u) ^ 2) = (n : ℝ) * ((c - u)⁻¹) ^ (n + 1) := by
      rw [neg_neg, one_div, ← inv_pow, mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hval] at h4
    exact h4
  have hint : IntervalIntegrable
      (fun u => (n : ℝ) * ((c - u)⁻¹) ^ (n + 1)) volume
      (-(2⁻¹ : ℝ)) (2⁻¹ : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num : -(2⁻¹ : ℝ) ≤ 2⁻¹)] at hu
    have hpos : c - u ≠ 0 := by
      have := hu.2
      have h : 0 < c - u := by linarith
      exact h.ne'
    exact (continuousAt_const.mul (((continuousAt_const.sub
      continuousAt_id).inv₀ hpos).pow _)).continuousWithinAt
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  have hend : ((c - -(2⁻¹ : ℝ))⁻¹) ^ n = ((c + 2⁻¹)⁻¹) ^ n := by
    rw [show c - -(2⁻¹ : ℝ) = c + 2⁻¹ from by ring]
  rw [hend] at hftc
  rw [eq_div_iff hn0]
  linear_combination hftc

/-- **The resolvent hierarchy**: for `n ≥ 1` and `z > 1`,
`∫ (z-x)^{-(n+1)} dμ_up
  = (2ⁿ/n)·(∫ ((2z-1)-x)⁻ⁿ dμ_up - ∫ ((2z+1)-x)⁻ⁿ dμ_up)`. -/
theorem integral_pow_inv_sub_succ (F : BoundedFabius)
    (hF : IsFabius F) {z : ℝ} (hz : 1 < z) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, ((z - x)⁻¹) ^ (n + 1) ∂(rvachevMeasure F) =
      (2 ^ n / n) *
        ((∫ x, (((2 * z - 1) - x)⁻¹) ^ n ∂(rvachevMeasure F)) -
          ∫ x, (((2 * z + 1) - x)⁻¹) ^ n ∂(rvachevMeasure F)) := by
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
    conv_lhs => rw [rvachevMeasure_refinement F hF]
    exact MeasureTheory.Measure.conv_comm _ _
  have hint : Integrable (fun x => ((z - x)⁻¹) ^ (n + 1))
      ((((rvachevMeasure F).map (2⁻¹ * ·)) ∗
        (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) : Measure ℝ)) := by
    rw [← href]
    exact integrable_pow_inv_sub_rvachevMeasure F hF habs (n + 1)
  have hintA : Integrable (fun x => (((2 * z - 1) - x)⁻¹) ^ n)
      (rvachevMeasure F) :=
    integrable_pow_inv_sub_rvachevMeasure F hF
      (by rw [abs_of_pos (by linarith)]; linarith) n
  have hintB : Integrable (fun x => (((2 * z + 1) - x)⁻¹) ^ n)
      (rvachevMeasure F) :=
    integrable_pow_inv_sub_rvachevMeasure F hF
      (by rw [abs_of_pos (by linarith)]; linarith) n
  calc ∫ x, ((z - x)⁻¹) ^ (n + 1) ∂(rvachevMeasure F)
      = ∫ x, ((z - x)⁻¹) ^ (n + 1)
          ∂((((rvachevMeasure F).map (2⁻¹ * ·)) ∗
            (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) : Measure ℝ)) := by
        rw [← href]
    _ = ∫ x, ∫ u, ((z - (x + u))⁻¹) ^ (n + 1)
          ∂(volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹))
          ∂((rvachevMeasure F).map (2⁻¹ * ·)) :=
        by exact MeasureTheory.integral_conv hint
    _ = ∫ x, ((((z - x) - 2⁻¹)⁻¹) ^ n -
            (((z - x) + 2⁻¹)⁻¹) ^ n) / n
          ∂((rvachevMeasure F).map (2⁻¹ * ·)) := by
        refine integral_congr_ae ?_
        have hae : ∀ᵐ x ∂((rvachevMeasure F).map (2⁻¹ * ·)),
            x ∈ Ioo (-(2⁻¹ : ℝ)) 2⁻¹ := by
          refine (MeasureTheory.ae_map_iff
            (measurable_const_mul _).aemeasurable
            measurableSet_Ioo).mpr ?_
          filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x' hx'
          exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
        filter_upwards [hae] with x hx
        have hc : 2⁻¹ < z - x := by
          have := hx.2
          linarith
        have hin : ∀ u : ℝ,
            ((z - (x + u))⁻¹) ^ (n + 1) =
              (((z - x) - u)⁻¹) ^ (n + 1) := fun u => by
          congr 2
          ring
        simp_rw [hin]
        exact integral_pow_inv_sub_uniform_half hc hn
    _ = ∫ x', (((z - 2⁻¹ * x' - 2⁻¹)⁻¹) ^ n -
            ((z - 2⁻¹ * x' + 2⁻¹)⁻¹) ^ n) / n
          ∂(rvachevMeasure F) := by
        have hmeas : Measurable fun x : ℝ =>
            ((((z - x) - 2⁻¹)⁻¹) ^ n -
              (((z - x) + 2⁻¹)⁻¹) ^ n) / n :=
          ((((measurable_const.sub measurable_id).sub
            measurable_const).inv.pow_const n).sub
            (((measurable_const.sub measurable_id).add
              measurable_const).inv.pow_const n)).div_const _
        rw [MeasureTheory.integral_map
          (measurable_const_mul _).aemeasurable
          hmeas.aestronglyMeasurable]
    _ = ∫ x', (2 ^ n / n) *
            ((((2 * z - 1) - x')⁻¹) ^ n -
              (((2 * z + 1) - x')⁻¹) ^ n)
          ∂(rvachevMeasure F) := by
        refine integral_congr_ae
          (Filter.Eventually.of_forall fun x' => ?_)
        dsimp only
        have e1 : z - 2⁻¹ * x' - 2⁻¹ = ((2 * z - 1) - x') / 2 := by
          ring
        have e2 : z - 2⁻¹ * x' + 2⁻¹ = ((2 * z + 1) - x') / 2 := by
          ring
        have hsc : ∀ a : ℝ, ((a / 2)⁻¹) ^ n = 2 ^ n * (a⁻¹) ^ n := by
          intro a
          rw [inv_div, div_pow, division_def, ← inv_pow]
        rw [e1, e2, hsc, hsc]
        ring
    _ = (2 ^ n / n) *
          ((∫ x, (((2 * z - 1) - x)⁻¹) ^ n ∂(rvachevMeasure F)) -
            ∫ x, (((2 * z + 1) - x)⁻¹) ^ n ∂(rvachevMeasure F)) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_sub hintA hintB]

end Fabius
