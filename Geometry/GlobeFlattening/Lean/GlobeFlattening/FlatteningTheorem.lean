import GlobeFlattening.ScalarConstruction
import GlobeFlattening.SphereDifferential
import GlobeFlattening.SphereLocalExcess
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Almost-everywhere isometric flattening of the cut sphere
-/

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology MeasureTheory

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
  have hne : cutSphere.Nonempty := ⟨spherePoint (0, 0), spherePoint_mapsTo
    (by simp [sphereLongitudeDomain, chartRectangle, Real.pi_pos])⟩
  exact (csSup_le (hne.image _) (forall_mem_image.2 hbound)).trans_lt hd

/-- The scalar function and its full-measure good set give the spherical
homeomorphism and the quantitative conclusions. -/
def globeFlattening_from_scalar
    {ε : ℝ} (hε : 0 < ε) {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    (hcu : ContinuousOn u sphereClosedBox)
    (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain)
    (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hclose : ∀ q ∈ sphereClosedBox, dist (flattenCoordinates u q) (sinusoidalCoordinates q) ≤ ε)
    (hSlope : StrictLowerSlopeOn u Real.cos sphereClosedBox)
    (hDeriv : ∀ p ∈ good, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p) :
    GlobeFlatteningResult ε := by
  have hab := neg_lt_self Real.pi_pos
  have hmono := strictMonoOn_chartRows_of_lowerSlope (fun _ => Real.cos_nonneg_of_mem_Icc) hSlope
  let g := triangularChart hab.le hcu hmono
  have hgimage : flattenCoordinates u '' sphereLongitudeDomain = g.target := g.image_source_eq_target
  let h := g.transHomeomorph planarEuclideanEquiv.toHomeomorph
  have hT : _ = h.target := planarEuclideanEquiv.image_eq_preimage_symm g.target
  let Z := sphereExceptional good
  have hZsub : Z ⊆ cutSphere := sdiff_subset
  let f := sphereFlattenForward u
  let fInv := spherePoint ∘ h.symm
  let F : cutSphere ≃ₜ h.target := sphereLongitudeChart.symm.trans h.toHomeomorphSourceTarget
  have hfopen : Topology.IsOpenEmbedding (cutSphere.restrict f) :=
    h.open_target.isOpenEmbedding_subtypeVal.comp F.isOpenEmbedding
  have hfcont : ContinuousOn f cutSphere := continuousOn_iff_continuous_restrict.2 hfopen.continuous
  have hfleft : LeftInvOn fInv f cutSphere :=
    fun w hw => congrArg Subtype.val (F.symm_apply_apply ⟨w, hw⟩)
  have hvol : volume h.target = volume g.target := hT ▸ volume_planarEuclideanEquiv_image _
  have hgoodSource : cutSphere \ Z = spherePoint '' good :=
    sdiff_sdiff_cancel_left (spherePoint_mapsTo.mono_left hsub).image_subset
  obtain ⟨hZmeas, hZnull⟩ := sphereExceptional_measurable_null hgood hsub hnull
  have hBorelImage {s} (hs : MeasurableSet s) (hss : s ⊆ cutSphere) : MeasurableSet (f '' s) := by
    simpa only [image_restrict, inter_eq_left.2 hss] using
      hfopen.measurableEmbedding.measurableSet_image' (hs.preimage measurable_subtype_coe)
  have hexcess (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : IsOpen V) (hne : V.Nonempty)
      (hVsub : V ⊆ h.target) : 0 < volume (V ∩ f '' Z) :=
    volume_sphereExceptional_inter_of_open hcu hSlope hgood hsub hnull hDeriv hV hne
      (hgimage.symm ▸ hT.symm ▸ hVsub)
  have hInv (p : ℝ × ℝ) (hp : p ∈ good) :
      HasFDerivAt fInv (sphereTangentLift p) (f (spherePoint p)) := by
    simpa only [f, g, triangularChart_apply, sphereFlattenForward_spherePoint (hsub hp)] using!
      hasFDerivAt_sphereFlatten_inverse g (hsub hp) (Real.cos_pos_of_mem_Ioo (hsub hp).2).ne'
        ((hDeriv p hp).prodMk hasFDerivAt_snd)
  refine
    { target := h.target
      exceptional := Z
      homeomorph := F
      forward := f
      inverse := fInv
      forward_agrees := fun p => rfl
      inverse_agrees := fun q => rfl
      target_open := h.open_target
      target_bounded := hT ▸ planarEuclideanEquiv.toContinuousLinearMap.lipschitz.isBounded_image (by
        rw [← hgimage]
        exact ((isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
          (hcu.prodMk continuous_snd.continuousOn)).isBounded.subset
            (image_mono sphereLongitudeDomain_subset_box))
      exceptional_subset := hZsub
      exceptional_measurable := hZmeas
      exceptional_null := hZnull
      target_area_lower := hvol.symm ▸ lintegral_cos_chartRectangle ▸
        lintegral_cos_lt_volume_chartImage hab (neg_lt_self (half_pos Real.pi_pos)) hcu
          (fun _ hy => (Real.cos_pos_of_mem_Ioo hy).le) hSlope
      target_area_upper :=
        hvol.symm ▸ volume_chartImage_upper_of_sinusoidal_closeness hε hcu hclose
      exceptional_image_measurable := hBorelImage hZmeas hZsub
      good_image_measurable := hBorelImage (measurableSet_cutSphere.diff hZmeas) sdiff_subset
      good_image_area := by
        rw [hgoodSource, sphereFlattenForward_image hsub, volume_planarEuclideanEquiv_image]
        exact (measure_flattened_good_image hgood hsub hnull g.injOn
          (fun p hp => (hDeriv p hp).hasFDerivWithinAt)
          (fun _ hp => (Real.cos_pos_of_mem_Ioo (hsub hp).2).le)).trans lintegral_cos_chartRectangle
      forward_derivative := ?_
      inverse_derivative := ?_
      distance_bound := ?_
      no_lipschitz_patch := by
        intro U hU hne K hLip
        have hLip' := (lipschitzOnWith_restrict (f := f).1 hLip).mono
          (inter_subset_inter_left _ hZsub)
        have hpos := hexcess _ (hfopen.isOpenMap _ hU) (hne.image _)
          (image_subset_iff.2 fun p _ => (F p).2)
        rw [← image_image_val_eq_restrict_image, inter_comm,
          ← hfleft.injOn.image_inter hZsub image_val_subset] at hpos
        refine hpos.ne' (Measure.absolutelyContinuous_isAddHaarMeasure volume (μH[(2 : ℕ)]) ?_)
        have hHaus : μH[2] (Z ∩ Subtype.val '' U) = 0 :=
          measure_mono_null inter_subset_left (hausdorffMeasure_sphereExceptional_eq_zero hsub hnull)
        simpa [hHaus] using hLip'.hausdorffMeasure_image_le (d := 2) (by norm_num)
      exceptional_area_positive := hexcess }
  · simp only [hgoodSource, forall_mem_image]
    exact fun p hp => ⟨sphereFlattenDerivative p,
      hasFDerivWithinAt_sphereFlatten hfcont hfleft (spherePoint_mapsTo (hsub hp)) (hInv p hp),
      fun _ h => norm_sphereFlattenDerivative_of_tangent p h⟩
  · simp only [hgoodSource, forall_mem_image]
    exact fun p hp => ⟨sphereTangentLift p, hInv p hp, fun v => by
      simp [hfleft (spherePoint_mapsTo (hsub hp)), tangent_sphereTangentLift, norm_sphereTangentLift]⟩
  · refine ⟨ε, lt_two_mul_self hε, fun w hw => ?_⟩
    exact (dist_planarEuclideanEquiv_of_snd_eq (by rfl)).trans_le
      (hclose _ (sphereLongitudeDomain_subset_box (sphereChartInverse_mapsTo hw)))

/-- The cut sphere has the usual total area of the unit sphere. -/
theorem sphericalArea_cutSphere : sphericalArea cutSphere = ENNReal.ofReal (4 * Real.pi) := by
  rw [← spherePoint_bijOn.image_eq, sphericalArea_spherePoint_image
    isOpen_sphereLongitudeDomain.measurableSet Subset.rfl, lintegral_cos_chartRectangle]

/-- For every positive tolerance a cut unit sphere has a flattening with the
area, differential, approximation and local distortion properties above. -/
theorem exists_globe_flattening {ε : ℝ} (hε : 0 < ε) :
    Nonempty (GlobeFlatteningResult ε) := by
  obtain ⟨u, E, hcu, hE, hsub, hnull, hclose, hSlope, hDeriv⟩ := exists_strict_scalar_flattening hε
  exact ⟨globeFlattening_from_scalar hε hcu hE hsub hnull hclose hSlope hDeriv⟩

end

end GlobeFlattening
