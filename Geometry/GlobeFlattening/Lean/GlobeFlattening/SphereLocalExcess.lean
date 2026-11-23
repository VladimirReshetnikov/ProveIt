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

open MeasureTheory Set Topology
open scoped NNReal ENNReal MeasureTheory Topology

noncomputable section

abbrev sphereFlattenForward (u : ℝ × ℝ → ℝ) :=
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
  let g := planarEuclideanEquiv ∘ flattenCoordinates u
  have hopen : IsOpen (sphereLongitudeDomain ∩ g ⁻¹' W) :=
    ContinuousOn.isOpen_inter_preimage (planarEuclideanEquiv.continuous.comp_continuousOn
      ((hu.mono sphereLongitudeDomain_subset_box).prodMk continuous_snd.continuousOn))
      isOpen_sphereLongitudeDomain hW
  rw [image_image] at hWsub
  obtain ⟨p, hp⟩ := image_inter_nonempty_iff.mp (hne.mono (subset_inter hWsub Subset.rfl))
  obtain ⟨a, b, c, d, hp', hbox⟩ := exists_chartClosedRectangle_subset_of_mem_nhds (hopen.mem_nhds hp)
  have hrectangle := chartRectangle_subset_closed.trans hbox
  have hab := hp'.1.1.trans hp'.1.2
  have hcd := hp'.2.1.trans hp'.2.2
  have hsubBox := hbox.trans (inter_subset_left.trans sphereLongitudeDomain_subset_box)
  have hcos (y : ℝ) (hy : y ∈ Icc c d) : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_mem_Icc (hsubBox (show (a, y) ∈ _ from ⟨⟨le_rfl, hab.le⟩, hy⟩)).2
  have hslope' (p) (hp) (q) (hq) := hslope p (hsubBox hp) q (hsubBox hq)
  let r := triangularChart hab.le (hu.mono hsubBox) (strictMonoOn_chartRows_of_lowerSlope hcos hslope')
  have hpos : 0 < volume (r '' (r.source \ good)) := by
    have hnull' : volume (r.source \ good) = 0 :=
      measure_mono_null (sdiff_subset_sdiff_left (hrectangle.trans inter_subset_left)) hnull
    rw [r.injOn.image_sdiff, r.image_source_eq_target]
    refine (tsub_pos_of_lt ?_).trans_le le_measure_sdiff
    exact (measure_flattened_good_image (r.open_source.measurableSet.inter hgood)
      inter_subset_left (by rwa [sdiff_self_inter]) r.injOn
      (fun p hp => (hderiv p hp.2).hasFDerivWithinAt)
      (fun p hp => hcos p.2 (Ioo_subset_Icc_self hp.1.2))).trans_lt
        (lintegral_cos_lt_volume_chartImage hab hcd (hu.mono hsubBox)
          (fun y hy => hcos y (Ioo_subset_Icc_self hy)) hslope')
  rw [← volume_planarEuclideanEquiv_image, image_image] at hpos
  rw [sphereExceptional_eq_image hsub, sphereFlattenForward_image sdiff_subset, image_image]
  exact hpos.trans_le <| measure_mono <| image_subset_iff.2 fun p hp =>
    let hpatch := hrectangle hp.1
    ⟨hpatch.2, mem_image_of_mem g ⟨hpatch.1, hp.2⟩⟩

/-- The chart-null exceptional set also has zero two-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_sphereExceptional_eq_zero {good : Set (ℝ × ℝ)}
    (hsub : good ⊆ sphereLongitudeDomain) (hnull : volume (sphereLongitudeDomain \ good) = 0) :
    μH[2] (sphereExceptional good) = 0 := by
  rw [sphereExceptional_eq_image hsub]
  apply le_zero_iff.mp
  simpa [hausdorffMeasure_prod_real, hnull] using
    lipschitzWith_spherePoint.hausdorffMeasure_image_le (d := 2) (by norm_num)
      (sphereLongitudeDomain \ good)

end

end GlobeFlattening
