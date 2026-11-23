import GlobeFlattening.TriangularChart
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Ioo c d
  · have heq : (fun x => (x, y)) ⁻¹' chartImage u a b c d = Ioo (u (a, y)) (u (b, y)) := by
      ext x
      exact and_iff_right hy
    rw [heq, Real.volume_Ioo, indicator_of_mem hy]
  · have heq : (fun x => (x, y)) ⁻¹' chartImage u a b c d = ∅ := by
      ext x
      simp only [chartImage, mem_preimage, mem_setOf_eq, hy, false_and, mem_empty_iff_false]
    rw [heq, measure_empty, indicator_of_notMem hy]

/-- Integrate the cosine density by horizontal slices of a rectangle. -/
theorem lintegral_cos_rectangle {a b c d : ℝ} (hab : a ≤ b) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal ((b - a) * Real.cos y) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.cos p.2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_cos.measurable.comp measurable_snd)
  rw [chartRectangle, Measure.volume_eq_prod, setLIntegral_prod_symm _ hmeas.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro y _
  change (∫⁻ _ in Ioo a b, ENNReal.ofReal (Real.cos y)) = _
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, mul_comm]
  exact (ENNReal.ofReal_mul (sub_nonneg.mpr hab)).symm

private abbrev latitudeInterval : Set ℝ := Ioo (-(Real.pi / 2)) (Real.pi / 2)

private theorem lintegral_latitude_affine_cos {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) :
    (∫⁻ y in latitudeInterval, ENNReal.ofReal (C * Real.cos y + B)) =
      ENNReal.ofReal (2 * C + Real.pi * B) := by
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hmul : Continuous (fun y => C * Real.cos y) := continuous_const.mul Real.continuous_cos
  have hsum : Continuous (fun y => C * Real.cos y + B) := hmul.add continuous_const
  have hint : IntegrableOn (fun y => C * Real.cos y + B) latitudeInterval :=
    hsum.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict latitudeInterval] (fun y => C * Real.cos y + B) :=
    (ae_restrict_mem measurableSet_Ioo).mono fun y hy =>
      add_nonneg (mul_nonneg hC (Real.cos_pos_of_mem_Ioo hy).le) hB
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  change ENNReal.ofReal (∫ y in Ioo _ _, C * Real.cos y + B) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_add (hmul.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_cos, Real.sin_neg,
    Real.sin_pi_div_two, intervalIntegral.integral_const]
  congr 1
  simp only [smul_eq_mul]
  ring

/-- The spherical area density integrates to `4π` over the cut-sphere
coordinate rectangle. -/
theorem lintegral_cos_chartRectangle :
    (∫⁻ p in chartRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2),
        ENNReal.ofReal (Real.cos p.2)) = ENNReal.ofReal (4 * Real.pi) := by
  rw [lintegral_cos_rectangle (by linarith [Real.pi_pos]), show Real.pi - -Real.pi = 2 * Real.pi by ring]
  simpa only [add_zero, mul_zero, show (2 : ℝ) * (2 * Real.pi) = 4 * Real.pi by ring] using
    lintegral_latitude_affine_cos (C := 2 * Real.pi) (B := 0) (by positivity) le_rfl

/-- A co-null good subset of the coordinate rectangle has image area
exactly `4π` when the prescribed scalar derivative holds there. -/
theorem volume_good_image_eq_four_pi
    {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    (hgood : MeasurableSet good)
    (hsub : good ⊆ chartRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2))
    (hnull : volume
      (chartRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2) \ good) = 0)
    (hinj : InjOn (flattenCoordinates u)
      (chartRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)))
    (hderiv : ∀ p ∈ good, HasFDerivWithinAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (chartRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)) p) :
    volume (flattenCoordinates u '' good) = ENNReal.ofReal (4 * Real.pi) :=
  (measure_flattened_good_image hgood hsub hnull hinj hderiv
    (fun _ hp => (Real.cos_pos_of_mem_Ioo (hsub hp).2).le)).trans lintegral_cos_chartRectangle

/-- The two endpoint errors give the uniform upper and lower bounds on
the length of every horizontal slice in the cut-sphere chart. -/
theorem chartWidth_bounds_of_closeness
    {u : ℝ × ℝ → ℝ} {δ y : ℝ}
    (hclose : ∀ p ∈ chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2),
      |u p - (Real.cos p.2 + δ) * p.1| ≤ δ)
    (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    2 * Real.pi * Real.cos y + 2 * (Real.pi - 1) * δ ≤ u (Real.pi, y) - u (-Real.pi, y) ∧
      u (Real.pi, y) - u (-Real.pi, y) ≤ 2 * Real.pi * Real.cos y + 2 * (Real.pi + 1) * δ := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hL := abs_le.mp (hclose (-Real.pi, y) ⟨⟨le_rfl, hπ⟩, hy⟩)
  have hR := abs_le.mp (hclose (Real.pi, y) ⟨⟨hπ, le_rfl⟩, hy⟩)
  constructor
  · linarith only [hL.2, hR.1]
  · linarith only [hL.1, hR.2]

/-- Two-sided area bound for the entire image of the scalar construction. -/
theorem volume_chartImage_bounds_of_closeness
    {u : ℝ × ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ContinuousOn u (chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)))
    (hclose : ∀ p ∈ chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2),
      |u p - (Real.cos p.2 + δ) * p.1| ≤ δ) :
    ENNReal.ofReal (4 * Real.pi + 2 * Real.pi * (Real.pi - 1) * δ) ≤
        volume (chartImage u (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)) ∧
      volume (chartImage u (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)) ≤
        ENNReal.ofReal (4 * Real.pi + 2 * Real.pi * (Real.pi + 1) * δ) := by
  rw [volume_chartImage_eq_lintegral_width (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi) hu]
  have hwidth (k : ℝ) (hk : 0 ≤ k) :
      (∫⁻ y in latitudeInterval, ENNReal.ofReal (2 * Real.pi * Real.cos y + 2 * k * δ)) =
        ENNReal.ofReal (4 * Real.pi + 2 * Real.pi * k * δ) := by
    rw [lintegral_latitude_affine_cos (by positivity) (by positivity)]
    congr 1
    ring
  constructor
  · rw [← hwidth (Real.pi - 1) (by linarith [Real.pi_gt_three])]
    exact setLIntegral_mono' measurableSet_Ioo
      (fun y hy => ENNReal.ofReal_le_ofReal (chartWidth_bounds_of_closeness hclose
        (Ioo_subset_Icc_self hy)).1)
  · rw [← hwidth (Real.pi + 1) (by positivity)]
    exact setLIntegral_mono' measurableSet_Ioo
      (fun y hy => ENNReal.ofReal_le_ofReal (chartWidth_bounds_of_closeness hclose
        (Ioo_subset_Icc_self hy)).2)

/-- The scalar refinement parameter used for a prescribed final tolerance. -/
def globeErrorParameter (ε : ℝ) : ℝ := min (ε / 3) (1 / 2)

theorem globeErrorParameter_bounds {ε : ℝ} (hε : 0 < ε) :
    0 < globeErrorParameter ε ∧ globeErrorParameter ε < 1 ∧ globeErrorParameter ε ≤ ε / 3 := by
  exact ⟨lt_min (by linarith) (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
    min_le_left _ _⟩

theorem volume_chartImage_with_tolerance
    {u : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hu : ContinuousOn u (chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)))
    (hclose : ∀ p ∈ chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2),
      |u p - (Real.cos p.2 + globeErrorParameter ε) * p.1| ≤ globeErrorParameter ε) :
    ENNReal.ofReal (4 * Real.pi) <
        volume (chartImage u (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)) ∧
      volume (chartImage u (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)) <
        ENNReal.ofReal (4 * Real.pi * (1 + ε)) := by
  obtain ⟨hδ, -, hδupper⟩ := globeErrorParameter_bounds hε
  obtain ⟨hlo, hhi⟩ := volume_chartImage_bounds_of_closeness hδ.le hu hclose
  have hπsub : 0 < Real.pi - 1 := by linarith [Real.pi_gt_three]
  have hπadd : 0 < Real.pi + 1 := by linarith [Real.pi_pos]
  have hexcess : 0 < 2 * Real.pi * (Real.pi - 1) * globeErrorParameter ε := by positivity
  have hfrom : 4 * Real.pi < 4 * Real.pi + 2 * Real.pi * (Real.pi - 1) * globeErrorParameter ε :=
    lt_add_of_pos_right _ hexcess
  have hto : 4 * Real.pi + 2 * Real.pi * (Real.pi + 1) * globeErrorParameter ε <
      4 * Real.pi * (1 + ε) := by
    have hscale := mul_le_mul_of_nonneg_left hδupper
      (show 0 ≤ 2 * Real.pi * (Real.pi + 1) by positivity)
    have hstrict := mul_lt_mul_of_pos_right (show Real.pi + 1 < 6 by linarith [Real.pi_lt_four])
      (show 0 < Real.pi * ε by positivity)
    linarith only [hscale, hstrict]
  constructor
  · exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hfrom).trans_le hlo
  · exact hhi.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hto)

/-- The sinusoidal projection written in the cut-sphere coordinates. -/
def sinusoidalCoordinates (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * Real.cos p.2, p.2)

/-- The same point-independent error bound holds throughout the coordinate
rectangle. In particular the supremum of the coordinate errors is below
`2ε`. -/
theorem flattenCoordinates_close_to_sinusoidal
    {u : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hclose : ∀ p ∈ chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2),
      |u p - (Real.cos p.2 + globeErrorParameter ε) * p.1| ≤ globeErrorParameter ε) :
    (∀ p ∈ chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2),
      dist (flattenCoordinates u p) (sinusoidalCoordinates p) ≤ (1 + Real.pi) * globeErrorParameter ε) ∧
      (1 + Real.pi) * globeErrorParameter ε < 2 * ε := by
  obtain ⟨hδ, -, hδupper⟩ := globeErrorParameter_bounds hε
  have hπ : 0 < Real.pi := Real.pi_pos
  constructor
  · intro p hp
    have hx : |p.1| ≤ Real.pi := abs_le.mpr hp.1
    rw [Prod.dist_eq, flattenCoordinates, sinusoidalCoordinates, dist_self,
      max_eq_left dist_nonneg, Real.dist_eq]
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
  · have hscale := mul_le_mul_of_nonneg_left hδupper (show 0 ≤ 1 + Real.pi by linarith)
    have hstrict := mul_lt_mul_of_pos_right (show 1 + Real.pi < 6 by linarith [Real.pi_lt_four]) hε
    linarith only [hscale, hstrict]

end

end GlobeFlattening
