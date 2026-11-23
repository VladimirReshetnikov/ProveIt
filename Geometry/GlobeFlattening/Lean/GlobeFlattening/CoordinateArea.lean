import GlobeFlattening.TriangularChart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Area and closeness in longitude and latitude coordinates

The entire image is measured by its horizontal interval lengths. On the
good set the restricted Jacobian formula instead gives the cosine density.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace GlobeFlattening

noncomputable section

/-- Horizontal slices of the image are the open intervals between the
endpoint values. Their lengths give its area. -/
theorem volume_chartImage_eq_lintegral_width
    {u : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (chartClosedRectangle a b c d)) :
    volume (chartImage u a b c d) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal (u (b, y) - u (a, y)) := by
  refine (Measure.measurePreserving_swap.measure_preimage_equiv
    (f := MeasurableEquiv.prodComm) _).trans ?_
  have hprofile (x : ℝ) (hx : x ∈ Icc a b) :=
    ((continuousOn_latitudeProfile hu hx).mono Ioo_subset_Icc_self).aemeasurable (μ := volume) measurableSet_Ioo
  exact volume_regionBetween_eq_lintegral (hprofile a ⟨le_rfl, hab⟩)
    (hprofile b ⟨hab, le_rfl⟩) measurableSet_Ioo

/-- Integrate the cosine density by horizontal slices of a rectangle. -/
theorem lintegral_cos_rectangle {a b c d : ℝ} (hab : a ≤ b) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal ((b - a) * Real.cos y) := by
  rw [chartRectangle, Measure.volume_eq_prod, setLIntegral_prod_symm _ (by fun_prop)]
  simp [Real.volume_Ioo, ENNReal.ofReal_mul (sub_nonneg.mpr hab), mul_comm]

/-- A strict longitude slope bound gives greater image area than the cosine density. -/
theorem lintegral_cos_lt_volume_chartImage
    {u : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hcos : ∀ y ∈ Ioo c d, 0 ≤ Real.cos y)
    (hslope : ∀ p ∈ chartClosedRectangle a b c d, ∀ q ∈ chartClosedRectangle a b c d,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) <
      volume (chartImage u a b c d) := by
  rw [lintegral_cos_rectangle hab.le, volume_chartImage_eq_lintegral_width hab.le hu]
  refine lintegral_strict_mono
    (Measure.restrict_eq_zero.not.mpr ((Measure.measure_Ioo_pos volume).2 hcd).ne')
    ((((continuousOn_latitudeProfile hu ⟨hab.le, le_rfl⟩).sub
      (continuousOn_latitudeProfile hu ⟨le_rfl, hab.le⟩)).mono Ioo_subset_Icc_self).aemeasurable
      measurableSet_Ioo).ennreal_ofReal
    (((continuous_const.mul Real.continuous_cos).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).lintegral_lt_top.ne) ?_
  refine (ae_restrict_mem measurableSet_Ioo).mono fun y hy => ?_
  have hy' := Ioo_subset_Icc_self hy
  apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg (sub_nonneg.mpr hab.le) (hcos y hy)) |>.2
  simpa only [mul_comm (b - a)] using
    hslope (a, y) ⟨⟨le_rfl, hab.le⟩, hy'⟩ (b, y) ⟨⟨hab.le, le_rfl⟩, hy'⟩ rfl hab

private abbrev latitudeInterval : Set ℝ := Ioo (-(Real.pi / 2)) (Real.pi / 2)

private theorem lintegral_sinusoidalWidth :
    (∫⁻ y in latitudeInterval, ENNReal.ofReal (2 * Real.pi * Real.cos y)) =
      ENNReal.ofReal (4 * Real.pi) := by
  simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have harea := lintegral_abs_det_fderiv_eq_addHaar_image volume
    (s := latitudeInterval) measurableSet_Ioo
    (fun y _ => (Real.hasDerivAt_sin y).hasFDerivAt.hasFDerivWithinAt)
    (Real.strictMonoOn_sin.injOn.mono Ioo_subset_Icc_self)
  simp only [ContinuousLinearMap.det_toSpanSingleton] at harea
  rw [setLIntegral_congr_fun measurableSet_Ioo
      (fun y hy => congrArg ENNReal.ofReal (abs_of_pos (Real.cos_pos_of_mem_Ioo hy)).symm),
    harea, ContinuousOn.image_Ioo_of_strictMonoOn (neg_lt_self (half_pos Real.pi_pos)).le
      Real.continuous_sin.continuousOn Real.strictMonoOn_sin, Real.volume_Ioo,
    Real.sin_neg, Real.sin_pi_div_two, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The spherical area density integrates to `4π` over the cut-sphere
coordinate rectangle. -/
theorem lintegral_cos_chartRectangle :
    (∫⁻ p in sphereLongitudeDomain,
        ENNReal.ofReal (Real.cos p.2)) = ENNReal.ofReal (4 * Real.pi) := by
  rw [sphereLongitudeDomain, lintegral_cos_rectangle (neg_le_self Real.pi_pos.le), sub_neg_eq_add,
    ← two_mul, lintegral_sinusoidalWidth]

/-- Scale the scalar error so its contribution to the uniform distance is `ε`. -/
def globeErrorParameter (ε : ℝ) : ℝ := ε / (1 + Real.pi)

theorem globeErrorParameter_pos {ε : ℝ} (hε : 0 < ε) : 0 < globeErrorParameter ε :=
  div_pos hε (by positivity)

/-- The sinusoidal projection written in the cut-sphere coordinates. -/
def sinusoidalCoordinates (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * Real.cos p.2, p.2)

private theorem dist_flattenCoordinates_sinusoidalCoordinates (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    dist (flattenCoordinates u p) (sinusoidalCoordinates p) = |u p - p.1 * Real.cos p.2| :=
  dist_prod_same_right.trans (Real.dist_eq _ _)

/-- A uniform sinusoidal distance bound gives at most two endpoint errors per slice. -/
theorem volume_chartImage_upper_of_sinusoidal_closeness
    {u : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hu : ContinuousOn u sphereClosedBox)
    (hclose : ∀ p ∈ sphereClosedBox,
      dist (flattenCoordinates u p) (sinusoidalCoordinates p) ≤ ε) :
    volume (chartImage u (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)) <
      ENNReal.ofReal (4 * Real.pi * (1 + ε)) := by
  have hab := neg_le_self Real.pi_pos.le
  rw [volume_chartImage_eq_lintegral_width hab hu]
  calc
    _ ≤ ∫⁻ y in latitudeInterval, ENNReal.ofReal (2 * Real.pi * Real.cos y) + ENNReal.ofReal (2 * ε) := by
      refine setLIntegral_mono' measurableSet_Ioo fun y hy =>
        (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
      have hleft := hclose (-Real.pi, y) ⟨⟨le_rfl, hab⟩, Ioo_subset_Icc_self hy⟩
      have hright := hclose (Real.pi, y) ⟨⟨hab, le_rfl⟩, Ioo_subset_Icc_self hy⟩
      rw [dist_flattenCoordinates_sinusoidalCoordinates] at hleft hright
      linarith only [(abs_le.mp hleft).1, (abs_le.mp hright).2]
    _ < _ := by
      rw [lintegral_add_right _ measurable_const, lintegral_sinusoidalWidth, setLIntegral_const,
        Real.volume_Ioo, sub_neg_eq_add, add_halves,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by
        nlinarith only [mul_pos Real.pi_pos hε])

/-- The scalar tolerance gives a uniform bound on the projection error. -/
theorem flattenCoordinates_close_to_sinusoidal
    {u : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hclose : ∀ p ∈ sphereClosedBox,
      |u p - (Real.cos p.2 + globeErrorParameter ε) * p.1| ≤ globeErrorParameter ε) :
    ∀ p ∈ sphereClosedBox,
      dist (flattenCoordinates u p) (sinusoidalCoordinates p) ≤ ε := by
  have hδ := globeErrorParameter_pos hε
  intro p hp
  rw [dist_flattenCoordinates_sinusoidalCoordinates,
    ← mul_div_cancel₀ ε (by positivity : 1 + Real.pi ≠ 0), add_mul, one_mul, mul_comm Real.pi]
  refine (abs_sub_le _ ((Real.cos p.2 + globeErrorParameter ε) * p.1) _).trans
    (add_le_add (hclose p hp) ?_)
  rw [mul_comm p.1, ← sub_mul, add_sub_cancel_left, abs_mul, abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr hp.1) hδ.le

end

end GlobeFlattening
