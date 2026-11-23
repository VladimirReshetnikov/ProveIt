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
  have hopen : IsOpen (sphereLongitudeDomain ∩ g ⁻¹' W) :=
    ContinuousOn.isOpen_inter_preimage (planarEuclideanEquiv.continuous.comp_continuousOn
      ((hu.mono sphereLongitudeDomain_subset_box).prodMk continuous_snd.continuousOn))
      isOpen_sphereLongitudeDomain hW
  rw [image_image] at hWsub
  obtain ⟨p, hp⟩ := image_inter_nonempty_iff.mp (hne.mono (subset_inter hWsub Subset.rfl))
  obtain ⟨a, b, c, d, hp', hbox⟩ := exists_chartClosedRectangle_subset_of_mem_nhds (hopen.mem_nhds hp)
  have hpos := volume_local_exceptional_image_pos (hp'.1.1.trans hp'.1.2)
    (hp'.2.1.trans hp'.2.2) (hbox.trans inter_subset_left) hu hslope hgood hnull hderiv
  rw [← volume_planarEuclideanEquiv_image, image_image] at hpos
  rw [sphereFlattenForward_exceptional_image hsub, image_image, ← image_preimage_inter,
    inter_sdiff_left_comm, ← inter_sdiff_assoc]
  exact hpos.trans_le (measure_mono (image_mono
    (sdiff_subset_sdiff_left (chartRectangle_subset_closed.trans hbox))))

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
  let Z' : Set cutSphere := Subtype.val ⁻¹' Z
  have himage : Subtype.val '' Z' = Z := image_preimage_eq_of_subset (by simpa using hZ)
  have hnull : μH[2] Z' = 0 := by
    rw [← isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num)), himage, hZnull]
  have heq : cutSphere.restrict f '' Z' = f '' Z := by
    rw [Set.restrict_eq, Set.image_comp, himage]
  have hpos := hexcess _ (hf.isOpenMap _ hU) (hne.image _)
    (Set.image_subset_iff.2 fun p _ => hmaps p.2)
  rw [← heq, ← image_inter hf.injective] at hpos
  refine hpos.ne' (Measure.absolutelyContinuous_isAddHaarMeasure volume
    (μH[Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))]) ?_)
  simpa [measure_mono_null inter_subset_right hnull] using
    (hLip.mono (inter_subset_left : U ∩ Z' ⊆ U)).hausdorffMeasure_image_le (d := 2) (by norm_num)

end

end GlobeFlattening
