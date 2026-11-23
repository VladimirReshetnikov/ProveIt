import GlobeFlattening.LocalExcess
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

open MeasureTheory Set
open scoped NNReal ENNReal MeasureTheory

noncomputable section

abbrev sphereFlattenForward (u : ℝ × ℝ → ℝ) :=
  planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse)

private abbrev sphereClosedCoordinates : Set (ℝ × ℝ) :=
  chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)

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
    (hu : ContinuousOn u sphereClosedCoordinates)
    (hslope : ∀ p ∈ sphereClosedCoordinates, ∀ q ∈ sphereClosedCoordinates,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hgood : MeasurableSet good) (hsub : good ⊆ sphereLongitudeDomain)
    (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ planarEuclideanEquiv '' (flattenCoordinates u '' sphereLongitudeDomain)) :
    0 < volume (W ∩
      (planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse)) '' sphereExceptional good) := by
  let V := planarEuclideanEquiv ⁻¹' W
  have hV : IsOpen V := hW.preimage planarEuclideanEquiv.continuous
  have hVne : V.Nonempty := hne.preimage planarEuclideanEquiv.surjective
  have hVsub : V ⊆ flattenCoordinates u '' sphereLongitudeDomain := by
    simpa only [preimage_image_eq _ planarEuclideanEquiv.injective] using
      preimage_mono (f := planarEuclideanEquiv) hWsub
  rw [sphereFlattenForward_exceptional_image hsub, ← image_preimage_inter,
    volume_planarEuclideanEquiv_image]
  exact volume_exceptional_inter_of_open hu hslope hgood hnull hderiv hV hVne hVsub

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
    {target : Set (EuclideanSpace ℝ (Fin 2))} (F : cutSphere ≃ₜ target)
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)}
    (hf : ∀ p : cutSphere, f p = (F p).val) (htarget : IsOpen target)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : Z ⊆ cutSphere) (hZnull : μH[2] Z = 0)
    (hexcess : ∀ W, IsOpen W → W.Nonempty → W ⊆ target → 0 < volume (W ∩ f '' Z))
    {U : Set cutSphere} (hU : IsOpen U) (hne : U.Nonempty) (K : ℝ≥0) :
    ¬ LipschitzOnWith K (fun p : cutSphere => f p) U := by
  intro hLip
  let A : cutSphere → EuclideanSpace ℝ (Fin 2) := fun p => f p
  let Z' : Set cutSphere := Subtype.val ⁻¹' Z
  have hA : A = Subtype.val ∘ F := funext hf
  have hpatch : A '' U = Subtype.val '' (F '' U) := by
    rw [hA, image_image]
    rfl
  have hOpen : IsOpen (A '' U) := hpatch ▸
    htarget.isOpenMap_subtype_val _ (F.isOpenMap _ hU)
  have hsub : A '' U ⊆ target := hpatch ▸ Subtype.coe_image_subset _ _
  have hpos := hexcess _ hOpen (hne.image A) hsub
  have hZ' : Subtype.val '' Z' = Z := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hZ]
  have hZ'null : μH[2] Z' = 0 := by
    rwa [← isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num)) Z', hZ']
  have hbound := (hLip.mono (inter_subset_left : U ∩ Z' ⊆ U)).hausdorffMeasure_image_le
    (d := 2) (by norm_num)
  have hHaar : Measure.IsAddHaarMeasure (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))) := by
    convert (inferInstance : Measure.IsAddHaarMeasure (μH[Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 2))] : Measure (EuclideanSpace ℝ (Fin 2)))) using 1
    simp
  have hzero : volume (A '' (U ∩ Z')) = 0 :=
    Measure.absolutelyContinuous_isAddHaarMeasure volume _ (le_zero_iff.mp <| by
      simpa [measure_mono_null inter_subset_right hZ'null] using hbound)
  have hBad : A '' Z' = f '' Z := by rw [← hZ', image_image]
  have hInj : Function.Injective A := hA ▸ Subtype.coe_injective.comp F.injective
  rw [image_inter hInj, hBad] at hzero
  exact hpos.ne' hzero

end

end GlobeFlattening
