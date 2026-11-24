import GlobeFlattening.CoordinateArea
import GlobeFlattening.RestrictedArea
import GlobeFlattening.SphereMeasure
import GlobeFlattening.SphereMetric
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Local distortion of the spherical flattening

Transfer the coordinate results to open patches of the sphere and of
the Euclidean target.
-/

namespace GlobeFlattening

open MeasureTheory Set
open scoped MeasureTheory

noncomputable abbrev sphereFlattenForward (u : ℝ × ℝ → ℝ) :=
  planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse)

theorem sphereFlattenForward_spherePoint {u : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ sphereLongitudeDomain) :
    sphereFlattenForward u (spherePoint p) =
      planarEuclideanEquiv (flattenCoordinates u p) :=
  congrArg (planarEuclideanEquiv ∘ flattenCoordinates u) (sphereChartInverse_spherePoint hp)

theorem sphereFlattenForward_image {u : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : s ⊆ sphereLongitudeDomain) :
    sphereFlattenForward u '' (spherePoint '' s) =
      planarEuclideanEquiv '' (flattenCoordinates u '' s) := by
  rw [image_image, image_image]
  exact image_congr fun _ hp => sphereFlattenForward_spherePoint (hs hp)

/-- Every nonempty open patch of the Euclidean target contains positive
area from the exceptional image. -/
theorem volume_sphereExceptional_inter_of_open {u : ℝ × ℝ → ℝ}
    {good : Set (ℝ × ℝ)} {W : Set (EuclideanSpace ℝ (Fin 2))}
    (hu : ContinuousOn u sphereClosedBox)
    (hslope : StrictLowerSlopeOn u Real.cos sphereClosedBox)
    (hgood : MeasurableSet good) (hsub : good ⊆ sphereLongitudeDomain)
    (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ planarEuclideanEquiv '' (flattenCoordinates u '' sphereLongitudeDomain)) :
    0 < volume (W ∩ sphereFlattenForward u '' sphereExceptional good) := by
  rw [inter_comm, sphereExceptional_eq_image hsub, sphereFlattenForward_image sdiff_subset,
    ← image_inter_preimage, volume_planarEuclideanEquiv_image, ← image_inter_preimage, sdiff_inter_right_comm]
  have hopen := ((hu.mono sphereLongitudeDomain_subset_box).prodMk
    continuous_snd.continuousOn).isOpen_inter_preimage isOpen_sphereLongitudeDomain
      (hW.preimage planarEuclideanEquiv.continuous)
  obtain ⟨z, hz⟩ := hne
  rcases hWsub hz with ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨a, b, c, d, hp', hbox⟩ := exists_chartClosedRectangle_subset_of_mem_nhds (hopen.mem_nhds ⟨hp, hz⟩)
  have hrectangle := chartRectangle_subset_closed.trans hbox
  obtain ⟨hab, hcd⟩ := (prod_nonempty_iff.1 ⟨p, hp'⟩).imp nonempty_Ioo.1 nonempty_Ioo.1
  have hsubBox := hbox.trans (inter_subset_left.trans sphereLongitudeDomain_subset_box)
  have hcos (y : ℝ) (hy : y ∈ Icc c d) : 0 ≤ Real.cos y :=
    (Real.cos_pos_of_mem_Ioo (hbox (a := (a, y)) ⟨left_mem_Icc.mpr hab.le, hy⟩).1.2).le
  have hslope' (p) (hp) (q) (hq) := hslope p (hsubBox hp) q (hsubBox hq)
  let r := triangularChart hab.le (hu.mono hsubBox) (strictMonoOn_chartRows_of_lowerSlope hcos hslope')
  refine lt_of_lt_of_le (b := volume (r '' (r.source \ good))) ?_
    (measure_mono (image_mono (sdiff_subset_sdiff_left hrectangle)))
  rw [r.injOn.image_sdiff, r.image_source_eq_target]
  refine (tsub_pos_of_lt ?_).trans_le le_measure_sdiff
  exact (measure_flattened_good_image (r.open_source.measurableSet.inter hgood) inter_subset_left (by
    rw [sdiff_self_inter]
    exact measure_mono_null (sdiff_subset_sdiff_left (hrectangle.trans inter_subset_left)) hnull) r.injOn
    (fun p hp => (hderiv p hp.2).hasFDerivWithinAt)
    (fun p hp => hcos p.2 (Ioo_subset_Icc_self hp.1.2))).trans_lt
      (lintegral_cos_lt_volume_chartImage hab hcd (hu.mono hsubBox)
        (fun y hy => hcos y (Ioo_subset_Icc_self hy)) hslope')

/-- The chart-null exceptional set also has zero two-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_sphereExceptional_eq_zero {good : Set (ℝ × ℝ)}
    (hsub : good ⊆ sphereLongitudeDomain) (hnull : volume (sphereLongitudeDomain \ good) = 0) :
    μH[2] (sphereExceptional good) = 0 := by
  rw [sphereExceptional_eq_image hsub]
  simpa [hausdorffMeasure_prod_real, hnull] using
    lipschitzWith_spherePoint.hausdorffMeasure_image_le (d := 2) (by norm_num)
      (sphereLongitudeDomain \ good)

end GlobeFlattening
