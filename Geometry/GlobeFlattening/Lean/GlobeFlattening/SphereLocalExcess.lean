import GlobeFlattening.CoordinateArea
import GlobeFlattening.SphereMeasure
import GlobeFlattening.SphereMetric
import Mathlib.MeasureTheory.Measure.Haar.Unique
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
      planarEuclideanEquiv (flattenCoordinates u p) := by
  simp only [Function.comp_apply, sphereChartInverse_spherePoint hp]

theorem sphereFlattenForward_image {u : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : s ⊆ sphereLongitudeDomain) :
    sphereFlattenForward u '' (spherePoint '' s) =
      planarEuclideanEquiv '' (flattenCoordinates u '' s) := by
  rw [image_image, image_image]
  exact image_congr fun _ hp => sphereFlattenForward_spherePoint (hs hp)

theorem sphereFlattenForward_exceptional_image {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    (hsub : good ⊆ sphereLongitudeDomain) :
    sphereFlattenForward u '' sphereExceptional good =
      planarEuclideanEquiv '' (flattenCoordinates u '' (sphereLongitudeDomain \ good)) := by
  rw [sphereExceptional_eq_image hsub, sphereFlattenForward_image sdiff_subset]

/-- Every nonempty open patch of the Euclidean target contains positive
area from the exceptional image. -/
theorem volume_sphereExceptional_inter_of_open {u : ℝ × ℝ → ℝ}
    {good : Set (ℝ × ℝ)} {W : Set (EuclideanSpace ℝ (Fin 2))}
    (hu : ContinuousOn u sphereClosedBox)
    (hslope : ∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hgood : MeasurableSet good) (hsub : good ⊆ sphereLongitudeDomain)
    (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ planarEuclideanEquiv '' (flattenCoordinates u '' sphereLongitudeDomain)) :
    0 < volume (W ∩
      (planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse)) '' sphereExceptional good) := by
  let g := planarEuclideanEquiv ∘ flattenCoordinates u
  let V := sphereLongitudeDomain ∩ g ⁻¹' W
  have hcont : ContinuousOn g sphereLongitudeDomain :=
    planarEuclideanEquiv.continuous.comp_continuousOn
      ((hu.mono sphereLongitudeDomain_subset_box).prodMk continuous_snd.continuousOn)
  have hV : IsOpen V := hcont.isOpen_inter_preimage isOpen_sphereLongitudeDomain hW
  obtain ⟨z, hz⟩ := hne
  rw [image_image] at hWsub
  obtain ⟨p, hp, rfl⟩ := hWsub hz
  obtain ⟨a, b, c, d, hp', hbox⟩ :=
    exists_chartClosedRectangle_subset_of_mem_nhds (hV.mem_nhds ⟨hp, hz⟩)
  have hpos := volume_local_exceptional_image_pos (hp'.1.1.trans hp'.1.2)
    (hp'.2.1.trans hp'.2.2) (hbox.trans inter_subset_left) hu hslope hgood hnull hderiv
  rw [← volume_planarEuclideanEquiv_image, image_image] at hpos
  rw [sphereFlattenForward_exceptional_image hsub, image_image, ← image_preimage_inter]
  exact hpos.trans_le (measure_mono (image_mono fun _ ⟨hq, hq'⟩ =>
    let ⟨hqdom, hqW⟩ := hbox (chartRectangle_subset_closed hq)
    ⟨hqW, hqdom, hq'⟩))

/-- The chart-null exceptional set also has zero two-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_sphereExceptional_eq_zero {good : Set (ℝ × ℝ)}
    (hsub : good ⊆ sphereLongitudeDomain) (hnull : volume (sphereLongitudeDomain \ good) = 0) :
    μH[2] (sphereExceptional good) = 0 := by
  rw [sphereExceptional_eq_image hsub]
  apply le_zero_iff.mp
  simpa [hausdorffMeasure_prod_real, hnull] using
    lipschitzWith_spherePoint.hausdorffMeasure_image_le (d := 2) (by norm_num)
      (sphereLongitudeDomain \ good)

/-- Positive exceptional image area in every open target patch precludes
Lipschitz bounds on open source patches. -/
theorem not_lipschitzOn_of_exceptional_area
    {target : Set (EuclideanSpace ℝ (Fin 2))}
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)}
    (hf : IsOpenEmbedding (cutSphere.restrict f)) (hmaps : MapsTo f cutSphere target)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : Z ⊆ cutSphere) (hZnull : μH[2] Z = 0)
    (hexcess : ∀ W, IsOpen W → W.Nonempty → W ⊆ target → 0 < volume (W ∩ f '' Z))
    {U : Set cutSphere} (hU : IsOpen U) (hne : U.Nonempty) (K : ℝ≥0) :
    ¬ LipschitzOnWith K (fun p : cutSphere => f p) U := by
  intro hLip
  let W := Subtype.val '' U
  have hWsub : W ⊆ cutSphere := Subtype.coe_image_subset _ _
  have hOpen : IsOpen (f '' W) := by
    rw [image_image]
    exact hf.isOpenMap _ hU
  have hsub : f '' W ⊆ target := (image_mono hWsub).trans hmaps.image_subset
  have hpos := hexcess _ hOpen ((hne.image _).image _) hsub
  have hLip' : LipschitzOnWith K f W :=
    inter_eq_right.mpr hWsub ▸ lipschitzOnWith_restrict.mp hLip
  have hbound := (hLip'.mono (inter_subset_left : W ∩ Z ⊆ W)).hausdorffMeasure_image_le
    (d := 2) (by norm_num)
  have hnull : μH[Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))] (f '' (W ∩ Z)) = 0 := by
    simpa [measure_mono_null inter_subset_right hZnull] using hbound
  rw [← (injOn_iff_injective.2 hf.injective).image_inter hWsub hZ] at hpos
  exact hpos.ne' (Measure.absolutelyContinuous_isAddHaarMeasure volume _ hnull)

end

end GlobeFlattening
