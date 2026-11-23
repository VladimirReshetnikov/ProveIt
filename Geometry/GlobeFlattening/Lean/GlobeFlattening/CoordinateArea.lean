import GlobeFlattening.TriangularChart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
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
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (isOpen_chartImage hab hu).measurableSet,
    ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun y => ?_
  change volume {x | y ∈ Ioo c d ∧ x ∈ Ioo (u (a, y)) (u (b, y))} = _
  by_cases hy : y ∈ Ioo c d <;>
    simp only [indicator_apply, hy, if_true, if_false, true_and, false_and, setOf_mem_eq,
      setOf_false, measure_empty, Real.volume_Ioo]

/-- Integrate the cosine density by horizontal slices of a rectangle. -/
theorem lintegral_cos_rectangle {a b c d : ℝ} (hab : a ≤ b) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal ((b - a) * Real.cos y) := by
  rw [chartRectangle, Measure.volume_eq_prod, setLIntegral_prod_symm _ (by fun_prop)]
  simp only [setLIntegral_const, Real.volume_Ioo, ENNReal.ofReal_mul (sub_nonneg.mpr hab)]
  exact lintegral_congr fun _ => mul_comm _ _

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

/-- On every open rectangle with closure inside the cut-sphere chart,
the exceptional image has positive planar measure. -/
theorem volume_local_exceptional_image_pos {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hbox : chartClosedRectangle a b c d ⊆ sphereLongitudeDomain)
    (hu : ContinuousOn u sphereClosedBox)
    (hslope : ∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p) :
    0 < volume (flattenCoordinates u '' (chartRectangle a b c d \ good)) := by
  have hsub := hbox.trans sphereLongitudeDomain_subset_box
  have hcos (y : ℝ) (hy : y ∈ Icc c d) : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_mem_Icc (hsub (show (a, y) ∈ _ from ⟨⟨le_rfl, hab.le⟩, hy⟩)).2
  have hslope' (p) (hp) (q) (hq) := hslope p (hsub hp) q (hsub hq)
  let g := triangularChart hab.le (hu.mono hsub) (strictMonoOn_chartRows_of_lowerSlope hcos hslope')
  have hnull' : volume (g.source \ good) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left (chartRectangle_subset_closed.trans hbox)) hnull
  have hAreaLt : (∫⁻ p in g.source, ENNReal.ofReal (Real.cos p.2)) < volume g.target :=
    lintegral_cos_lt_volume_chartImage hab hcd (hu.mono hsub)
      (fun y hy => hcos y (Ioo_subset_Icc_self hy)) hslope'
  rw [← g.image_source_eq_target,
    ← measure_flattened_good_image (g.open_source.measurableSet.inter hgood)
      inter_subset_left (by rwa [sdiff_self_inter]) g.injOn
      (fun p hp => (hderiv p hp.2).hasFDerivWithinAt)
      (fun p hp => hcos p.2 (Ioo_subset_Icc_self hp.1.2))] at hAreaLt
  change 0 < volume (g '' (g.source \ good))
  rw [g.injOn.image_sdiff]
  exact (tsub_pos_of_lt hAreaLt).trans_le le_measure_sdiff

private abbrev latitudeInterval : Set ℝ := Ioo (-(Real.pi / 2)) (Real.pi / 2)

private theorem lintegral_sinusoidalWidth :
    (∫⁻ y in latitudeInterval, ENNReal.ofReal (2 * Real.pi * Real.cos y)) =
      ENNReal.ofReal (4 * Real.pi) := by
  have hmono : StrictMonoOn (fun y => 2 * Real.pi * Real.sin y) (Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    (strictMono_mul_left_of_pos (by positivity)).comp_strictMonoOn Real.strictMonoOn_sin
  rw [lintegral_deriv_eq_volume_image_of_monotoneOn measurableSet_Ioo
    (fun y _ => ((Real.hasDerivAt_sin y).const_mul (2 * Real.pi)).hasDerivWithinAt)
    (hmono.monotoneOn.mono Ioo_subset_Icc_self),
    ContinuousOn.image_Ioo_of_strictMonoOn (by linarith [Real.pi_pos]) (by fun_prop) hmono,
    Real.volume_Ioo, Real.sin_neg, Real.sin_pi_div_two]
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
    _ < _ := by
      rw [lintegral_add_right _ measurable_const, lintegral_sinusoidalWidth, setLIntegral_const,
        Real.volume_Ioo, show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring,
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
  rw [dist_flattenCoordinates_sinusoidalCoordinates]
  have htri := abs_sub_le (u p) ((Real.cos p.2 + globeErrorParameter ε) * p.1) (p.1 * Real.cos p.2)
  rw [show (Real.cos p.2 + globeErrorParameter ε) * p.1 - p.1 * Real.cos p.2 =
    globeErrorParameter ε * p.1 by ring, abs_mul, abs_of_pos hδ] at htri
  rw [← globeErrorParameter_scale ε, add_mul, one_mul, mul_comm Real.pi]
  exact htri.trans (add_le_add (hclose p hp) (mul_le_mul_of_nonneg_left (abs_le.mpr hp.1) hδ.le))

end

end GlobeFlattening
