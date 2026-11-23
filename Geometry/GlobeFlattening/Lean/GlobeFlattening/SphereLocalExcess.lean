import GlobeFlattening.LocalExcess
import GlobeFlattening.SphereMeasure
import GlobeFlattening.SphereMetric

/-!
# Local distortion of the spherical flattening

Transfer the coordinate results to open patches of the sphere and of
the Euclidean target.
-/

namespace GlobeFlattening

open MeasureTheory Set
open scoped NNReal ENNReal

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

theorem sphereFlattenForward_exceptional_image {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    (hsub : good ⊆ sphereLongitudeDomain) :
    (planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse)) '' sphereExceptional good =
      planarEuclideanEquiv '' (flattenCoordinates u '' (sphereLongitudeDomain \ good)) := by
  simp only [sphereExceptional_eq_image hsub, image_image]
  exact (show EqOn (sphereFlattenForward u ∘ spherePoint)
      (planarEuclideanEquiv ∘ flattenCoordinates u) (sphereLongitudeDomain \ good) from
    fun _ hp => sphereFlattenForward_spherePoint hp.1).image_eq

/-- Every nonempty open patch of the Euclidean target contains positive
area from the exceptional image. -/
theorem volume_sphereExceptional_inter_of_open {u : ℝ × ℝ → ℝ}
    {good : Set (ℝ × ℝ)} {W : Set (EuclideanSpace ℝ (Fin 2))}
    (hu : ContinuousOn u sphereClosedCoordinates)
    (hslope : ∀ p ∈ sphereClosedCoordinates, ∀ q ∈ sphereClosedCoordinates,
      p.2 = q.2 → p.1 ≤ q.1 → Real.cos p.2 * (q.1 - p.1) ≤ u q - u p)
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

/-- The spherical flattening has no Lipschitz bound on any relatively open
nonempty subset of the cut sphere. -/
theorem not_lipschitzOn_sphereFlatten_of_open {u : ℝ × ℝ → ℝ}
    {good : Set (ℝ × ℝ)} {U : Set cutSphere}
    (hu : ContinuousOn u sphereClosedCoordinates)
    (hslope : ∀ p ∈ sphereClosedCoordinates, ∀ q ∈ sphereClosedCoordinates,
      p.2 = q.2 → p.1 ≤ q.1 → Real.cos p.2 * (q.1 - p.1) ≤ u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hU : IsOpen U) (hne : U.Nonempty) (K : ℝ≥0) :
    ¬ LipschitzOnWith K
      (fun w : cutSphere => (planarEuclideanEquiv ∘
        (flattenCoordinates u ∘ sphereChartInverse)) w) U := by
  intro hLip
  let U' := sphereLongitudeChart ⁻¹' U
  let V := Subtype.val '' U'
  have hV : IsOpen V := isOpen_sphereLongitudeDomain.isOpenMap_subtype_val U'
    (hU.preimage sphereLongitudeChart.continuous)
  have hVne : V.Nonempty := (hne.preimage sphereLongitudeChart.surjective).image _
  have hVsub : V ⊆ sphereLongitudeDomain := by
    rintro _ ⟨p, _, rfl⟩
    exact p.2
  let A := planarEuclideanEquiv.symm.toContinuousLinearMap
  have hchart : LipschitzWith 2 sphereLongitudeChart :=
    fun p q => lipschitzWith_spherePoint p.val q.val
  have hcomp := A.lipschitz.comp_lipschitzOnWith
    (hLip.comp hchart.lipschitzOnWith (mapsTo_preimage _ _))
  have hpull : LipschitzOnWith (‖A‖₊ * (K * 2))
      (sphereLongitudeDomain.restrict (flattenCoordinates u)) U' := by
    have hidentity (p : sphereLongitudeDomain) :
        A (sphereFlattenForward u (sphereLongitudeChart p)) = flattenCoordinates u p := by
      change planarEuclideanEquiv.symm (sphereFlattenForward u (spherePoint p)) = _
      rw [sphereFlattenForward_spherePoint p.2, ContinuousLinearEquiv.symm_apply_apply]
    intro p hp q hq
    have hbound := hcomp hp hq
    change edist (A (sphereFlattenForward u (sphereLongitudeChart p)))
      (A (sphereFlattenForward u (sphereLongitudeChart q))) ≤ _ at hbound
    rwa [hidentity p, hidentity q] at hbound
  have hflat := lipschitzOnWith_restrict.mp hpull
  rw [inter_eq_right.mpr hVsub] at hflat
  exact not_lipschitzOn_flattenCoordinates_of_open hu hslope hgood hnull hderiv
    hV hVne hVsub _ hflat

end

end GlobeFlattening
