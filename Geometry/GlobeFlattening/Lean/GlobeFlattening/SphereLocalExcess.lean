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

private abbrev sphereFlattenForward (u : ℝ × ℝ → ℝ) :=
  planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse)

private abbrev sphereClosedCoordinates : Set (ℝ × ℝ) :=
  chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)

private theorem sphereFlattenForward_spherePoint {u : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ sphereLongitudeDomain) :
    sphereFlattenForward u (spherePoint p) =
      planarEuclideanEquiv (flattenCoordinates u p) := by
  simp only [Function.comp_apply, sphereChartInverse_spherePoint hp]

theorem sphereFlattenForward_exceptional_image {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    (hsub : good ⊆ sphereLongitudeDomain) :
    (planarEuclideanEquiv ∘ (flattenCoordinates u ∘ sphereChartInverse)) '' sphereExceptional good =
      planarEuclideanEquiv '' (flattenCoordinates u '' (sphereLongitudeDomain \ good)) := by
  rw [sphereExceptional_eq_image hsub]
  ext w
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨flattenCoordinates u p, ⟨p, hp, rfl⟩, (sphereFlattenForward_spherePoint hp.1).symm⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨spherePoint p, ⟨p, hp, rfl⟩, sphereFlattenForward_spherePoint hp.1⟩

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
  have hVne : V.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨planarEuclideanEquiv.symm w, by simpa [V] using hw⟩
  have hVsub : V ⊆ flattenCoordinates u '' sphereLongitudeDomain := by
    intro v hv
    obtain ⟨v', hv', eq⟩ := hWsub hv
    rwa [planarEuclideanEquiv.injective eq] at hv'
  have hpos := volume_exceptional_inter_of_open hu hslope hgood hnull hderiv hV hVne hVsub
  let e := planarEuclideanEquiv.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume volume := measurePreserving_planarEuclideanEquiv
  rw [sphereFlattenForward_exceptional_image hsub, ← he.measure_preimage_equiv]
  change 0 < volume (planarEuclideanEquiv ⁻¹'
    (W ∩ planarEuclideanEquiv '' (flattenCoordinates u '' (sphereLongitudeDomain \ good))))
  rw [preimage_inter, planarEuclideanEquiv.injective.preimage_image]
  exact hpos

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
  have hVne : V.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨(sphereLongitudeChart.symm w).val, sphereLongitudeChart.symm w,
      by simpa [U'] using hw, rfl⟩
  have hVsub : V ⊆ sphereLongitudeDomain := by
    rintro _ ⟨p, _, rfl⟩
    exact p.2
  let A := planarEuclideanEquiv.symm.toContinuousLinearMap
  apply not_lipschitzOn_flattenCoordinates_of_open hu hslope hgood hnull hderiv hV hVne hVsub
    (‖A‖₊ * K * 2)
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have hidentity (z : sphereLongitudeDomain) :
      A (sphereFlattenForward u (sphereLongitudeChart z)) = flattenCoordinates u z := by
    change planarEuclideanEquiv.symm (sphereFlattenForward u (spherePoint z)) = _
    simp only [sphereFlattenForward_spherePoint z.2, ContinuousLinearEquiv.symm_apply_apply]
  rw [← hidentity p, ← hidentity q]
  have h₁ := A.lipschitz (sphereFlattenForward u (sphereLongitudeChart p))
    (sphereFlattenForward u (sphereLongitudeChart q))
  have h₂ := hLip hp hq
  have h₃ := lipschitzWith_spherePoint p.val q.val
  calc
    _ ≤ (↑‖A‖₊ : ℝ≥0∞) *
        edist (sphereFlattenForward u (sphereLongitudeChart p))
          (sphereFlattenForward u (sphereLongitudeChart q)) := h₁
    _ ≤ (↑‖A‖₊ : ℝ≥0∞) * (↑K * edist (spherePoint p) (spherePoint q)) :=
      mul_le_mul_right h₂ _
    _ ≤ (↑‖A‖₊ : ℝ≥0∞) * (↑K * ((2 : ℝ≥0∞) * edist p.val q.val)) :=
      mul_le_mul_right (mul_le_mul_right h₃ _) _
    _ = _ := by simp [mul_assoc]

end

end GlobeFlattening
