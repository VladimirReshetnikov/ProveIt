import GlobeFlattening.TriangularChart
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

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
  rw [chartImage, Measure.volume_eq_prod,
    Measure.measurePreserving_swap.measure_preimage_emb MeasurableEquiv.prodComm.measurableEmbedding]
  have hprofile (x : ℝ) (hx : x ∈ Icc a b) :
      AEMeasurable (fun y => u (x, y)) (volume.restrict (Ioo c d)) :=
    ((continuousOn_latitudeProfile hu hx).mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo
  exact volume_regionBetween_eq_lintegral
    (hprofile a ⟨le_rfl, hab⟩) (hprofile b ⟨hab, le_rfl⟩) measurableSet_Ioo

/-- Integrate the cosine density by horizontal slices of a rectangle. -/
theorem lintegral_cos_rectangle {a b c d : ℝ} (hab : a ≤ b) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal ((b - a) * Real.cos y) := by
  have hcos : Measurable (fun y => ENNReal.ofReal (Real.cos y)) :=
    ENNReal.measurable_ofReal.comp Real.continuous_cos.measurable
  rw [chartRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict,
    ← lintegral_map hcos measurable_snd, Measure.map_snd_prod, lintegral_smul_measure,
    Measure.restrict_apply_univ, Real.volume_Ioo, smul_eq_mul]
  simp_rw [ENNReal.ofReal_mul (sub_nonneg.mpr hab)]
  rw [lintegral_const_mul _ hcos]

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
  have hLcon : Continuous (fun y => (b - a) * Real.cos y) := continuous_const.mul Real.continuous_cos
  refine lintegral_strict_mono ?_
    (((continuousOn_chartWidth hab.le hu).mono Ioo_subset_Icc_self).aemeasurable
      measurableSet_Ioo).ennreal_ofReal
    (hLcon.integrableOn_Icc.mono_set Ioo_subset_Icc_self).lintegral_lt_top.ne ?_
  · exact Measure.restrict_eq_zero.not.mpr ((Measure.measure_Ioo_pos volume).2 hcd).ne'
  · refine (ae_restrict_mem measurableSet_Ioo).mono fun y hy => ?_
    have hy' := Ioo_subset_Icc_self hy
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg (sub_nonneg.mpr hab.le) (hcos y hy))).2
    simpa only [mul_comm (b - a)] using
      hslope (a, y) ⟨⟨le_rfl, hab.le⟩, hy'⟩ (b, y) ⟨⟨hab.le, le_rfl⟩, hy'⟩ rfl hab

private abbrev latitudeInterval : Set ℝ := Ioo (-(Real.pi / 2)) (Real.pi / 2)

private theorem lintegral_sinusoidalWidth :
    (∫⁻ y in latitudeInterval, ENNReal.ofReal (2 * Real.pi * Real.cos y)) =
      ENNReal.ofReal (4 * Real.pi) := by
  have hcont : Continuous (fun y => 2 * Real.pi * Real.cos y) :=
    continuous_const.mul Real.continuous_cos
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    ((ae_restrict_mem measurableSet_Ioo).mono fun y hy =>
      mul_nonneg (by positivity) (Real.cos_pos_of_mem_Ioo hy).le)]
  change ENNReal.ofReal (∫ y in Ioo _ _, 2 * Real.pi * Real.cos y) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_const_mul, integral_cos, Real.sin_neg, Real.sin_pi_div_two]
  congr 1
  ring

/-- The spherical area density integrates to `4π` over the cut-sphere
coordinate rectangle. -/
theorem lintegral_cos_chartRectangle :
    (∫⁻ p in sphereLongitudeDomain,
        ENNReal.ofReal (Real.cos p.2)) = ENNReal.ofReal (4 * Real.pi) := by
  rw [sphereLongitudeDomain, lintegral_cos_rectangle (by linarith [Real.pi_pos]), show Real.pi - -Real.pi = 2 * Real.pi by ring]
  exact lintegral_sinusoidalWidth

/-- A co-null good subset of the coordinate rectangle has image area
exactly `4π` when the prescribed scalar derivative holds there. -/
theorem volume_good_image_eq_four_pi
    {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain)
    (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hinj : InjOn (flattenCoordinates u) sphereLongitudeDomain)
    (hderiv : ∀ p ∈ good, HasFDerivWithinAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) sphereLongitudeDomain p) :
    volume (flattenCoordinates u '' good) = ENNReal.ofReal (4 * Real.pi) :=
  (measure_flattened_good_image hgood hsub hnull hinj hderiv
    (fun _ hp => (Real.cos_pos_of_mem_Ioo (hsub hp).2).le)).trans lintegral_cos_chartRectangle

/-- Scale the scalar error so its contribution to the uniform distance is `ε`. -/
def globeErrorParameter (ε : ℝ) : ℝ := ε / (1 + Real.pi)

theorem globeErrorParameter_pos {ε : ℝ} (hε : 0 < ε) : 0 < globeErrorParameter ε :=
  div_pos hε (by positivity)

private theorem globeErrorParameter_scale (ε : ℝ) :
    (1 + Real.pi) * globeErrorParameter ε = ε :=
  mul_div_cancel₀ ε (by positivity)

/-- The sinusoidal projection written in the cut-sphere coordinates. -/
def sinusoidalCoordinates (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * Real.cos p.2, p.2)

private theorem dist_flattenCoordinates_sinusoidalCoordinates (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    dist (flattenCoordinates u p) (sinusoidalCoordinates p) = |u p - p.1 * Real.cos p.2| := by
  rw [Prod.dist_eq, flattenCoordinates, sinusoidalCoordinates, dist_self,
    max_eq_left dist_nonneg, Real.dist_eq]

/-- A uniform sinusoidal distance bound gives at most two endpoint errors per slice. -/
theorem volume_chartImage_upper_of_sinusoidal_closeness
    {u : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hu : ContinuousOn u sphereClosedBox)
    (hclose : ∀ p ∈ sphereClosedBox,
      dist (flattenCoordinates u p) (sinusoidalCoordinates p) ≤ ε) :
    volume (chartImage u (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)) <
      ENNReal.ofReal (4 * Real.pi * (1 + ε)) := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [volume_chartImage_eq_lintegral_width hab hu]
  calc
    _ ≤ ∫⁻ y in latitudeInterval, ENNReal.ofReal (2 * Real.pi * Real.cos y) + ENNReal.ofReal (2 * ε) := by
      refine setLIntegral_mono' measurableSet_Ioo fun y hy =>
        (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
      have hleft := hclose (-Real.pi, y) ⟨⟨le_rfl, hab⟩, Ioo_subset_Icc_self hy⟩
      have hright := hclose (Real.pi, y) ⟨⟨hab, le_rfl⟩, Ioo_subset_Icc_self hy⟩
      rw [dist_flattenCoordinates_sinusoidalCoordinates] at hleft hright
      linarith only [(abs_le.mp hleft).1, (abs_le.mp hright).2]
    _ = ENNReal.ofReal (4 * Real.pi + 2 * Real.pi * ε) := by
      rw [lintegral_add_right _ measurable_const, lintegral_sinusoidalWidth, setLIntegral_const,
        Real.volume_Ioo, show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by
      linarith only [mul_pos Real.pi_pos hε])

/-- The scalar tolerance gives a uniform bound on the projection error. -/
theorem flattenCoordinates_close_to_sinusoidal
    {u : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hclose : ∀ p ∈ sphereClosedBox,
      |u p - (Real.cos p.2 + globeErrorParameter ε) * p.1| ≤ globeErrorParameter ε) :
    ∀ p ∈ sphereClosedBox,
      dist (flattenCoordinates u p) (sinusoidalCoordinates p) ≤ ε := by
  have hδ := globeErrorParameter_pos hε
  intro p hp
  have hx : |p.1| ≤ Real.pi := abs_le.mpr hp.1
  rw [dist_flattenCoordinates_sinusoidalCoordinates]
  have heq : u p - p.1 * Real.cos p.2 =
      (u p - (Real.cos p.2 + globeErrorParameter ε) * p.1) + globeErrorParameter ε * p.1 := by ring
  rw [heq]
  calc
    _ ≤ |u p - (Real.cos p.2 + globeErrorParameter ε) * p.1| +
        |globeErrorParameter ε * p.1| := abs_add_le ..
    _ ≤ globeErrorParameter ε + globeErrorParameter ε * Real.pi := by
      rw [abs_mul, abs_of_pos hδ]
      exact add_le_add (hclose p hp) (mul_le_mul_of_nonneg_left hx hδ.le)
    _ = (1 + Real.pi) * globeErrorParameter ε := by ring
    _ = ε := globeErrorParameter_scale ε

end

end GlobeFlattening
