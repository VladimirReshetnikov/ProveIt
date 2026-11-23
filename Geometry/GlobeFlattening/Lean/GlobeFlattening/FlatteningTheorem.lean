import GlobeFlattening.ScalarConstruction
import GlobeFlattening.SphereLocalExcess

/-!
# Almost-everywhere isometric flattening of the cut sphere
-/

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace GlobeFlattening

noncomputable section

/-- The usual sinusoidal map, expressed on the cut sphere via its
longitude-latitude coordinates. -/
def sinusoidalProjection : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
  planarEuclideanEquiv ∘ (sinusoidalCoordinates ∘ sphereChartInverse)

/-- The main quantitative conclusions for flattening the unit sphere cut
along a meridian. The ambient representatives allow the derivatives to be
stated in Euclidean spaces. They agree with the homeomorphism on its source
and target. -/
structure GlobeFlatteningResult (ε : ℝ) where
  target : Set (EuclideanSpace ℝ (Fin 2))
  exceptional : Set (EuclideanSpace ℝ (Fin 3))
  homeomorph : cutSphere ≃ₜ target
  forward : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)
  inverse : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)
  forward_agrees : ∀ p : cutSphere, forward p = (homeomorph p : EuclideanSpace ℝ (Fin 2))
  inverse_agrees : ∀ q : target, inverse q = (homeomorph.symm q : EuclideanSpace ℝ (Fin 3))
  target_open : IsOpen target
  target_bounded : Bornology.IsBounded target
  exceptional_subset : exceptional ⊆ cutSphere
  exceptional_measurable : MeasurableSet exceptional
  exceptional_null : sphericalArea exceptional = 0
  target_area_lower : ENNReal.ofReal (4 * Real.pi) < volume target
  target_area_upper : volume target < ENNReal.ofReal (4 * Real.pi * (1 + ε))
  exceptional_image_measurable : MeasurableSet (forward '' exceptional)
  good_image_measurable : MeasurableSet (forward '' (cutSphere \ exceptional))
  good_image_area : volume (forward '' (cutSphere \ exceptional)) = ENNReal.ofReal (4 * Real.pi)
  forward_derivative : ∀ p ∈ cutSphere \ exceptional,
    ∃ L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      HasFDerivWithinAt forward L cutSphere p ∧
        ∀ w : EuclideanSpace ℝ (Fin 3), ⟪p, w⟫ = 0 → ‖L w‖ = ‖w‖
  inverse_derivative : ∀ z ∈ forward '' (cutSphere \ exceptional),
    ∃ L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3),
      HasFDerivAt inverse L z ∧
        ∀ v : EuclideanSpace ℝ (Fin 2), ⟪inverse z, L v⟫ = 0 ∧ ‖L v‖ = ‖v‖
  distance_bound : ∃ d < 2 * ε, ∀ p ∈ cutSphere, dist (forward p) (sinusoidalProjection p) ≤ d
  no_lipschitz_patch : ∀ U : Set cutSphere, IsOpen U → U.Nonempty → ∀ K : ℝ≥0,
    ¬ LipschitzOnWith K (fun p : cutSphere => forward p) U
  exceptional_area_positive : ∀ V : Set (EuclideanSpace ℝ (Fin 2)),
    IsOpen V → V.Nonempty → V ⊆ target → 0 < volume (V ∩ forward '' exceptional)

/-- The point-independent bound also bounds the supremum over the cut sphere. -/
theorem GlobeFlatteningResult.sup_distance_lt {ε : ℝ} (result : GlobeFlatteningResult ε) :
    sSup ((fun p => dist (result.forward p) (sinusoidalProjection p)) '' cutSphere) < 2 * ε := by
  obtain ⟨d, hd, hbound⟩ := result.distance_bound
  have hp : (0, 0) ∈ sphereLongitudeDomain :=
    ⟨⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩,
      ⟨neg_lt_zero.mpr (half_pos Real.pi_pos), half_pos Real.pi_pos⟩⟩
  have hne : cutSphere.Nonempty := ⟨spherePoint (0, 0), spherePoint_mapsTo hp⟩
  exact (csSup_le (hne.image _) (by rintro _ ⟨p, hp, rfl⟩; exact hbound p hp)).trans_lt hd

/-- The scalar function and its full-measure good set give the spherical
homeomorphism and the quantitative conclusions. -/
def globeFlattening_from_scalar
    {ε : ℝ} (hε : 0 < ε) {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    (hcu : ContinuousOn u sphereClosedBox)
    (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain)
    (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hclose : ∀ q ∈ sphereClosedBox,
      |u q - (Real.cos q.2 + globeErrorParameter ε) * q.1| ≤ globeErrorParameter ε)
    (hSlope : ∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox, p.2 = q.2 → p.1 < q.1 →
      Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hDeriv : ∀ p ∈ good, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p) :
    GlobeFlatteningResult ε := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hmono := strictMonoOn_chartRows_of_lowerSlope (fun _ => Real.cos_nonneg_of_mem_Icc) hSlope
  let g := triangularChart hab hcu hmono
  let G := g.transHomeomorph planarEuclideanEquiv.toHomeomorph
  let Z := sphereExceptional good
  let f := sphereFlattenForward u
  let fInv := spherePoint ∘ G.symm
  let F : cutSphere ≃ₜ G.target := sphereLongitudeChart.symm.trans G.toHomeomorphSourceTarget
  have htarget : G.target = planarEuclideanEquiv '' g.target :=
    (planarEuclideanEquiv.toEquiv.image_eq_preimage_symm _).symm
  have hcloseCoordinates := flattenCoordinates_close_to_sinusoidal hε hclose
  have harea : ENNReal.ofReal (4 * Real.pi) < volume G.target ∧
      volume G.target < ENNReal.ofReal (4 * Real.pi * (1 + ε)) := by
    rw [htarget, volume_planarEuclideanEquiv_image]
    have hlo := lintegral_cos_lt_volume_chartImage
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
      (by linarith [Real.pi_pos] : -(Real.pi / 2) < Real.pi / 2) hcu
      (fun _ hy => (Real.cos_pos_of_mem_Ioo hy).le) hSlope
    exact ⟨lintegral_cos_chartRectangle ▸ hlo,
      volume_chartImage_upper_of_sinusoidal_closeness hε hcu hcloseCoordinates⟩
  have hgoodSource : cutSphere \ Z = spherePoint '' good :=
    sdiff_sdiff_cancel_left ((image_mono hsub).trans spherePoint_mapsTo.image_subset)
  have hgoodImage : f '' (cutSphere \ Z) = planarEuclideanEquiv '' (flattenCoordinates u '' good) := hgoodSource ▸
    sphereFlattenForward_image hsub
  have hPlaneImage {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hss : s ⊆ sphereLongitudeDomain) :
      MeasurableSet (planarEuclideanEquiv '' (flattenCoordinates u '' s)) := by
    rw [image_image]
    exact hs.image_of_continuousOn_injOn (G.continuousOn.mono hss) (G.injOn.mono hss)
  have hexcess (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : IsOpen V) (hne : V.Nonempty)
      (hVsub : V ⊆ G.target) : 0 < volume (V ∩ f '' Z) := by
    rw [htarget, ← g.image_source_eq_target] at hVsub
    exact volume_sphereExceptional_inter_of_open hcu hSlope hgood hsub hnull hDeriv hV hne hVsub
  have hInv (p : ℝ × ℝ) (hp : p ∈ good) :
      HasFDerivAt fInv (sphereTangentLift p) (planarEuclideanEquiv (g p)) :=
    hasFDerivAt_sphereFlatten_inverse g (hsub hp) (Real.cos_pos_of_mem_Ioo (hsub hp).2).ne'
      ((hDeriv p hp).prodMk hasFDerivAt_snd)
  refine
    { target := G.target
      exceptional := Z
      homeomorph := F
      forward := f
      inverse := fInv
      forward_agrees := fun p => rfl
      inverse_agrees := fun q => rfl
      target_open := G.open_target
      target_bounded := by
        rw [htarget]
        exact planarEuclideanEquiv.toContinuousLinearMap.lipschitz.isBounded_image
          (isBounded_chartImage hab hcu (fun y hy => hmono y (Ioo_subset_Icc_self hy)))
      exceptional_subset := sdiff_subset
      exceptional_measurable := measurableSet_sphereExceptional hgood hsub
      exceptional_null := measure_sphereExceptional_eq_zero hgood hsub hnull
      target_area_lower := harea.1
      target_area_upper := harea.2
      exceptional_image_measurable := by
        change MeasurableSet (sphereFlattenForward u '' sphereExceptional good)
        rw [sphereFlattenForward_exceptional_image hsub]
        exact hPlaneImage (isOpen_sphereLongitudeDomain.measurableSet.diff hgood) sdiff_subset
      good_image_measurable := hgoodImage.symm ▸ hPlaneImage hgood hsub
      good_image_area := by
        rw [hgoodImage, volume_planarEuclideanEquiv_image]
        exact volume_good_image_eq_four_pi hgood hsub hnull g.injOn
          (fun p hp => (hDeriv p hp).hasFDerivWithinAt)
      forward_derivative := ?_
      inverse_derivative := ?_
      distance_bound := ?_
      no_lipschitz_patch := fun _ hU hne K =>
        not_lipschitzOn_of_exceptional_area F (fun _ => rfl) G.open_target sdiff_subset
          (hausdorffMeasure_sphereExceptional_eq_zero hsub hnull) hexcess hU hne K
      exceptional_area_positive := hexcess }
  · intro w hw
    rw [hgoodSource] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    have hpoint := spherePoint_mapsTo (hsub hp)
    have hInv' : HasFDerivAt fInv (sphereTangentLift p) (f (spherePoint p)) := by
      rw [show f (spherePoint p) = planarEuclideanEquiv (g p) from
        sphereFlattenForward_spherePoint (hsub hp)]
      exact hInv p hp
    exact ⟨sphereFlattenDerivative p,
      hasFDerivWithinAt_sphereFlatten F (fun _ => rfl) (fun _ => rfl) hpoint hInv',
      fun _ h => norm_sphereFlattenDerivative_of_tangent p h⟩
  · intro z hz
    rw [hgoodImage] at hz
    obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := hz
    have hval : fInv (planarEuclideanEquiv (flattenCoordinates u p)) = spherePoint p :=
      congrArg spherePoint (G.left_inv (hsub hp))
    refine ⟨sphereTangentLift p, hInv p hp, fun v => ?_⟩
    exact ⟨hval.symm ▸ tangent_sphereTangentLift p v, norm_sphereTangentLift p v⟩
  · refine ⟨ε, by linarith, ?_⟩
    intro w hw
    let p := sphereChartInverse w
    have hsub' : p ∈ sphereClosedBox := sphereLongitudeDomain_subset_box (sphereChartInverse_mapsTo hw)
    change dist (planarEuclideanEquiv (flattenCoordinates u p))
      (planarEuclideanEquiv (sinusoidalCoordinates p)) ≤ _
    rw [dist_planarEuclideanEquiv_of_snd_eq
      (a := flattenCoordinates u p) (b := sinusoidalCoordinates p) rfl]
    exact hcloseCoordinates p hsub'

/-- The cut sphere has the usual total area of the unit sphere. -/
theorem sphericalArea_cutSphere : sphericalArea cutSphere = ENNReal.ofReal (4 * Real.pi) := by
  rw [← spherePoint_image_domain,
    sphericalArea_spherePoint_image isOpen_sphereLongitudeDomain.measurableSet Subset.rfl]
  exact lintegral_cos_chartRectangle

/-- For every positive tolerance a cut unit sphere has a flattening with the
area, differential, approximation and local distortion properties above. -/
theorem exists_globe_flattening {ε : ℝ} (hε : 0 < ε) :
    Nonempty (GlobeFlatteningResult ε) := by
  obtain ⟨u, E, hcu, hE, hsub, hnull, hclose, hSlope, hDeriv⟩ := exists_strict_scalar_flattening (globeErrorParameter_pos hε)
  exact ⟨globeFlattening_from_scalar hε hcu hE hsub hnull hclose hSlope hDeriv⟩

end

end GlobeFlattening
