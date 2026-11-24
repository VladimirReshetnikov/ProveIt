import GlobeFlattening.TriangularChart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (isOpen_chartImage hab hu).measurableSet,
    ← lintegral_indicator measurableSet_Ioo]
  exact lintegral_congr fun y => by
    by_cases hy : y ∈ Ioo c d <;> simp [-mem_Ioo, chartImage, hy, Real.volume_Ioo, preimage]

/-- Integrate the cosine density by horizontal slices of a rectangle. -/
theorem lintegral_cos_rectangle {a b c d : ℝ} (hab : a ≤ b) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal (Real.cos y * (b - a)) := by
  rw [chartRectangle, Measure.volume_eq_prod, setLIntegral_prod_symm _ (by fun_prop)]
  simp [Real.volume_Ioo, ENNReal.ofReal_mul' (sub_nonneg.mpr hab)]

/-- A strict longitude slope bound gives greater image area than the cosine density. -/
theorem lintegral_cos_lt_volume_chartImage
    {u : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hcos : ∀ y ∈ Ioo c d, 0 ≤ Real.cos y)
    (hslope : StrictLowerSlopeOn u Real.cos (chartClosedRectangle a b c d)) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) <
      volume (chartImage u a b c d) := by
  have hwidth := (continuousOn_latitudeProfile hu ⟨hab.le, le_rfl⟩).sub
    (continuousOn_latitudeProfile hu ⟨le_rfl, hab.le⟩)
  rw [lintegral_cos_rectangle hab.le, volume_chartImage_eq_lintegral_width hab.le hu]
  refine lintegral_strict_mono
    (Measure.restrict_eq_zero.not.mpr ((Measure.measure_Ioo_pos volume).2 hcd).ne')
    ((hwidth.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo).ennreal_ofReal
    (((Real.continuous_cos.mul continuous_const).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).lintegral_lt_top.ne) ?_
  refine (ae_restrict_mem measurableSet_Ioo).mono fun y hy => ?_
  have hy' := Ioo_subset_Icc_self hy
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg (hcos y hy) (sub_nonneg.mpr hab.le))).2
    (hslope (a, y) ⟨⟨le_rfl, hab.le⟩, hy'⟩ (b, y) ⟨⟨hab.le, le_rfl⟩, hy'⟩ rfl hab)

private abbrev latitudeInterval : Set ℝ := Ioo (-(Real.pi / 2)) (Real.pi / 2)

private theorem lintegral_sinusoidalWidth_add (r : ℝ) (hr : 0 ≤ r) :
    (∫⁻ y in latitudeInterval, ENNReal.ofReal (Real.cos y * (2 * Real.pi) + r)) =
      ENNReal.ofReal (4 * Real.pi + Real.pi * r) := by
  have hfi : IntervalIntegrable (fun y => Real.cos y * (2 * Real.pi) + r) volume
      (-(Real.pi / 2)) (Real.pi / 2) := Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← ofReal_integral_eq_lintegral_ofReal (hfi.1.mono_set Ioo_subset_Ioc_self)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun y hy =>
      add_nonneg (mul_nonneg (Real.cos_pos_of_mem_Ioo hy).le (by positivity)) hr),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (neg_le_self (half_pos Real.pi_pos).le),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => Real.sin y * (2 * Real.pi) + r * y)
      (fun y _ => ((Real.hasDerivAt_sin y).mul_const (2 * Real.pi)).add (hasDerivAt_const_mul r)) hfi]
  exact congrArg ENNReal.ofReal (by rw [Real.sin_neg, Real.sin_pi_div_two]; ring)

/-- The spherical area density integrates to `4π` over the cut-sphere
coordinate rectangle. -/
theorem lintegral_cos_chartRectangle :
    (∫⁻ p in sphereLongitudeDomain,
        ENNReal.ofReal (Real.cos p.2)) = ENNReal.ofReal (4 * Real.pi) := by
  simpa only [sphereLongitudeDomain, lintegral_cos_rectangle (neg_le_self Real.pi_pos.le),
    sub_neg_eq_add, ← two_mul, add_zero, mul_zero] using lintegral_sinusoidalWidth_add 0 le_rfl

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
    _ ≤ ∫⁻ y in latitudeInterval, ENNReal.ofReal (Real.cos y * (2 * Real.pi) + 2 * ε) := by
      refine setLIntegral_mono' measurableSet_Ioo fun y hy => ENNReal.ofReal_le_ofReal ?_
      have hleft := hclose (-Real.pi, y) ⟨⟨le_rfl, hab⟩, Ioo_subset_Icc_self hy⟩
      have hright := hclose (Real.pi, y) ⟨⟨hab, le_rfl⟩, Ioo_subset_Icc_self hy⟩
      rw [dist_flattenCoordinates_sinusoidalCoordinates] at hleft hright
      linarith only [(abs_le.mp hleft).1, (abs_le.mp hright).2]
    _ < _ := by
      rw [lintegral_sinusoidalWidth_add _ (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by
        nlinarith only [mul_pos Real.pi_pos hε])

end

end GlobeFlattening
