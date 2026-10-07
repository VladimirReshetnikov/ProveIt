import OAI.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorBudgetedConsumer
import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralProductivityEarlyGain

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_detected_canonical_native_source_with_bounds (m Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)],
      ∀ {P pnum pSlice u Qstride Eextra : ℝ} {nX : ℕ},
      0 < m → 0 ≤ P → 0 ≤ Eextra → pnum ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n, (boundedBooleanJetRows (Fin (0 + 1)) (b.1.val + 1)).card ≤
        Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ budget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
        gainLog ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧
        aDetect ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        Pk ∈ Set.Icc 0 budget ∧ Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp budget ∧
            Nonempty (AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis) (S := S) (nX := nX)
              P Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  obtain ⟨C, hC, hgeometry⟩ :=
    exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m 0 Cdetect
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ P pnum pSlice u Qstride Eextra nX hm hP hExtra hnum
    hvars hI hn hblocks hpSlice hu hQstride hnX A Pearly rowSets T siteRadius
    pModel pDetect aDetect D gainLog target Pk F Tmod δ E η Prho Ptail K budget
  obtain ⟨pRadius, R, hpRadius, hpRadBudget, hR, hrone, hT0, hTideal,
      hTsource, hTradius, hTbound, hrbound, hTbudget, hrbudget, hsmall,
      hdimensions, hPEarly, hEarlyBudget,
      hpModel, hpDetect, haDetect, htarget, hD, hgain, hPk, hPrho,
      hPtail, hTmod, ρ, hρ, t, ht, htone, htinv, htbudget, hcomparison,
      hsampler⟩ := hgeometry B hm (Nat.zero_le m) hP hExtra hnum
        hvars hI hn hblocks hpSlice hu hQstride hnX
  refine ⟨pRadius, R, hpRadius, hpRadBudget, hR, hpModel, hpDetect,
    hgain, htarget, haDetect, hD, hPk, hPrho, hPtail, t, ht, htone, ?_⟩
  intro J _ U basis Pscale
  obtain ⟨hPscale, hScaleLog, S, hRinv, htinv', hcount, hlength, hS, hcutoff⟩ :=
    hsampler U basis
  have hD1 : 1 ≤ D := by
    have hdim := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
    exact hm1.trans hdim
  have hkTail : Pk ≤ Ptail :=
    prepared_affineProfileToleranceEnvelope_kernel_bound hm
      canonicalSublevelCutoffLip canonicalTransitionLip hD1 hPk.1 htarget.1 hpDetect.1
  have hkScale : Pk ≤ Pscale := hkTail.trans (le_add_of_nonneg_left hpRadius.1)
  refine ⟨S, hPscale, hkScale, hS, ?_, ?_⟩
  · refine ⟨{
      hP := hPscale.1
      hRP := fun j => (hR j).2.1.trans (Real.one_le_exp hPscale.1)
      hRi := hRinv
      hσi := htinv'
      hcount := hcount
      hdimensions := hdimensions
      hPk := hPk.1
      hPrho := hPrho.1
      htarget := htarget.1
      hlength := ?_
      η := η
      hη0 := (Real.exp_pos _).le
      hηsmall := ?_
      ρ := ρ
      t := t
      htone := htone
      hs := hcomparison
      hρ := fun partition => (hρ partition).1
      hρ1 := fun partition => (hρ partition).2.1
      hρlog := fun partition => (hρ partition).2.2.1
      hσsmall := fun _ => le_rfl
      T := T
      hT := hTideal
      hsource := hTsource
      siteRadius := siteRadius
      hrone := hrone
      hradius := hTradius
      hbudgets := hsmall
      hK := ?_ }⟩
    · simp only [Fintype.card_fin]
      exact (Real.exp_le_exp.mpr (allocatedAffineLengthLog_prepared_density
        m D Pscale Prho Pk target pDetect Tmod)).trans hlength
    · change Real.exp (-E) ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))
      apply Real.exp_le_exp.mpr
      dsimp only [E]
      linarith
    · intro j
      simpa only [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le] using (hR j).2.2
  · intro α hα
    exact ⟨slicedDetectionGain_lower 0 Cdetect _ hα,
      slicedDetection_kernel_cutoff_bound 0 Cdetect _ G hpDetect.1 hpDetect.1 haDetect.1 hα,
      hcutoff α hα⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_preparedModularCanonicalDetector_prepared_source (m Cdetect : ℕ) :
    let Aearly := Classical.choose (exists_preparedModularCanonicalDetectorEarlyParameters m Cdetect)
    let _Cgeom := Classical.choose (exists_detected_canonical_native_source_with_bounds m Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → 0 ≤ P → pnum ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let _selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let coarseTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let τ := Real.exp (-Pphysical)
      let Rspatial := spatialPrimitiveEnvelope Pphysical coarseTarget 0
      let ξLog := 2 * (Rspatial + spatialTupleToleranceLog Rspatial) + 4
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + C) ^ C
      P ≤ budget ∧ Pearly ∈ Set.Icc 0 budget ∧
      Pphysical ∈ Set.Icc 0 budget ∧ coarseTarget ∈ Set.Icc 0 budget ∧
      ξLog ∈ Set.Icc 0 budget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ budget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
        gainLog ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧
        aDetect ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
        Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp budget ∧
            Nonempty (AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis) (S := S) (nX := nX)
              P Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  intro Aearly Cgeom
  obtain ⟨C, hC, hphysical⟩ := exists_detectedCanonicalPhysicalBudget m Aearly Cgeom
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hM Jalloc pnum P pSlice u Qstride hm hP hnum hpSlice hu hQstride hnX
    G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D gainLog Pk
    Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K budget
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hM
  have hpnum : pnum ∈ Set.Icc 0 P := ⟨Nat.cast_nonneg _, hnum⟩
  have hblocks (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin 1) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin 1) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets L Jalloc 0 (Nat.zero_le m) a
  obtain ⟨hPQ, hEarlyQ, hModelQ, hDetectQ, hAQ, hDQ, hGainQ, hPkQ⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorEarlyParameters m Cdetect)).2 (G := G) B hm hP hpnum (Nat.cast_le.mpr hvars)
      (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
      hblocks hpSlice hu hQstride hnX
  obtain ⟨hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
      hPhysBudget, hCoarseBudget, hExtraBudget, hTargetBudget, hξBudget, hGeomBudget⟩ :=
    hphysical nX hP hPkQ.1 hQstride.1 hGainQ.1 hPkQ.2
      (hQstride.2.trans hPQ) hGainQ.2 (hnX.trans hPQ)
  have hPhys0 : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    have hQ0 : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hQ0 hPkQ.1) hQstride.1) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (by norm_num)
  have hCoarse0 : 0 ≤ coarseTarget := by dsimp only [coarseTarget]; linarith only [hGainQ.1]
  have hξ0 : 0 ≤ ξLog := by
    have hRsp := (spatialPrimitiveEnvelope_bounds hPhys0 hCoarse0 (le_refl 0)).1
    have htsp := spatialTupleToleranceLog_nonneg hRsp
    dsimp only [ξLog]
    linarith only [hRsp, htsp]
  have hQphys : Qearly ≤ Pphysical := by
    dsimp only [Pphysical]
    have hk0 := hPkQ.1
    have hs0 := hQstride.1
    linarith only [hk0, hs0, Nat.cast_nonneg (α := ℝ) nX, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hQbudget : Qearly ≤ budget := hQphys.trans hPhysBudget
  refine ⟨hPQ.trans hQbudget, ⟨hEarlyQ.1, hEarlyQ.2.trans hQbudget⟩,
    ⟨hPhys0, hPhysBudget⟩, ⟨hCoarse0, hCoarseBudget⟩, ⟨hξ0, hξBudget⟩,
    hExtra, hprecision, hτ, hτhalf, hτdim, hτinv, ?_⟩
  obtain ⟨pRadius, R, hpRadius, hpRadBudget, hR, hpModel, hpDetect,
      hgain, htarget, haDetect, hD, hPk, hPrho, hPtail, t, ht, htone, hsampler⟩ :=
    (Classical.choose_spec (exists_detected_canonical_native_source_with_bounds m Cdetect)).2 (G := G) B (Eextra := Eextra) hm hP hExtra hpnum (Nat.cast_le.mpr hvars)
      (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
      hblocks hpSlice hu hQstride hnX
  refine ⟨pRadius, R, hpRadius, hpRadBudget.trans hGeomBudget, hR,
    ⟨hpModel.1, hpModel.2.trans hGeomBudget⟩,
    ⟨hpDetect.1, hpDetect.2.trans hGeomBudget⟩,
    ⟨hgain.1, hgain.2.trans hGeomBudget⟩,
    ⟨htarget.1, htarget.2.trans hGeomBudget⟩,
    ⟨haDetect.1, haDetect.2.trans hGeomBudget⟩,
    ⟨hD.1, hD.2.trans hGeomBudget⟩,
    ⟨hPk.1, hPk.2.trans hGeomBudget⟩,
    ⟨hPrho.1, hPrho.2.trans hGeomBudget⟩,
    ⟨hPtail.1, hPtail.2.trans hGeomBudget⟩,
    t, ht, htone, ?_⟩
  intro J _ U basis Pscale
  obtain ⟨S, hPscale, hkScale, hS, hgeometry, hgainKernel⟩ := hsampler U basis
  exact ⟨S, ⟨hPscale.1, hPscale.2.trans hGeomBudget⟩, hkScale,
    hS.trans (Real.exp_le_exp.mpr hGeomBudget), hgeometry, hgainKernel⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_preparedModularCanonicalDetector_initial_source (m Cdetect : ℕ) :
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Aearly := Classical.choose (exists_preparedModularCanonicalDetectorEarlyParameters m Cdetect)
    let _Cgeom := Classical.choose (exists_detected_canonical_native_source_with_bounds m Cdetect)
    let Csource := Classical.choose (exists_preparedModularCanonicalDetector_prepared_source m Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → 0 ≤ P → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let _selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (Palloc + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let coarseTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let τ := Real.exp (-Pphysical)
      let Rspatial := spatialPrimitiveEnvelope Pphysical coarseTarget 0
      let ξLog := 2 * (Rspatial + spatialTupleToleranceLog Rspatial) + 4
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let sourceBudget := (Palloc + Csource) ^ Csource
      let budget := (P + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ sourceBudget ≤ budget ∧
      Palloc ≤ sourceBudget ∧ Pearly ∈ Set.Icc 0 sourceBudget ∧
      Pphysical ∈ Set.Icc 0 sourceBudget ∧ coarseTarget ∈ Set.Icc 0 sourceBudget ∧
      ξLog ∈ Set.Icc 0 sourceBudget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ sourceBudget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 sourceBudget ∧ pDetect ∈ Set.Icc 0 sourceBudget ∧
        gainLog ∈ Set.Icc 0 sourceBudget ∧ target ∈ Set.Icc 0 sourceBudget ∧
        aDetect ∈ Set.Icc 0 sourceBudget ∧ D ∈ Set.Icc 0 sourceBudget ∧ Pk ∈ Set.Icc 0 sourceBudget ∧
        Prho ∈ Set.Icc 0 sourceBudget ∧ Ptail ∈ Set.Icc 0 sourceBudget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 sourceBudget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp sourceBudget ∧
            Nonempty (AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis) (S := S) (nX := nX)
              Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  intro Aalloc Aearly Cgeom Csource
  obtain ⟨C, hC, hcompose⟩ := exists_shiftedPower_triple_composition_budget Aalloc Csource 1
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Jalloc pnum P pSlice u Qstride hm hP hM hpSlice hu hQstride hnX
    Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D gainLog Pk
    Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K sourceBudget budget
  obtain ⟨hPalloc, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2 hP hM hnX
  have hPalloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hlift {z : ℝ} (hz : z ∈ Set.Icc 0 P) : z ∈ Set.Icc 0 Palloc :=
    ⟨hz.1, hz.2.trans hPalloc⟩
  have hBudget : sourceBudget ≤ budget := by
    have hcomp : sourceBudget + 1 ≤ budget := by
      simpa only [Nat.cast_one, pow_one] using hcompose hP
    linarith only [hcomp]
  refine ⟨hPalloc, hnum.2, hBudget, ?_⟩
  exact (Classical.choose_spec (exists_preparedModularCanonicalDetector_prepared_source m Cdetect)).2
    L hCoord hm hPalloc0 hnum.2 (hlift hpSlice) (hlift hu) (hlift hQstride) (hnX.trans hPalloc)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedModularCanonicalDetector_narrow_width_le_one
    (X T : Type*) [Fintype X] [Fintype T] {G : Type*} [Fintype G]
    {q : ℕ} (selection : Fin q ↪ G) (Mk : ℕ) (p E : ℝ) :
    normalizedTupleNarrowWidth X T selection Mk p E ≤ 1 := by
  exact min_le_left _ _

section Consumer

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (0 + 1))))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
local notation "α" => allocatedModelUnitThreshold u pModel Kslice Ctail
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (0 + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

def PreparedModularCanonicalDetectorConstructedInterface
    (Pchart Qstride Pmaster pGain Pphysical : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    let r := preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) Pmaster
    let coarseTarget := pGain + 32
    let τ := Real.exp (-Pphysical)
    let hτSpatial := Real.exp_pos (-Pphysical)
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let ξn := normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α)
      Pphysical coarseTarget
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp r.required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp r.required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    ∀ (hbases : bases.Nonempty),
    let hξn := normalizedTupleNarrowWidth_pos (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    (htotal : 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)) →
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW hτSpatial hξn stride cells hmass bases hbases htotal
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) 0 (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let budget := r.nativeBudget
    let hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect qDetect α) Pphysical coarseTarget
    ∃ hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i,
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial
      hξone N (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i)))
      hmargin e hrootSum
    ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Qmodel : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Qmodel i ∈ twistedNativeSampleFunctions (fun _ : Fin nX => 1) 0 budget
        (fun t : integerBox N => t.val)
        (fun (twist : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
            (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩)
          (t : integerBox N) => twist.eval N poly t.val)) ∧
      input = (∑ i, coeff i • Qmodel i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
      sampledSliceSeminorm pathLaw physical slices
        (fun z j t => star ((Vdetect z j).eval
          (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) err ≤ Real.exp (-u) ∧
      (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30)

end Consumer

theorem exists_preparedModularCanonicalDetector (m : ℕ) (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Aearly := Classical.choose (exists_preparedModularCanonicalDetectorEarlyParameters m Cdetect)
    let _Cgeom := Classical.choose (exists_detected_canonical_native_source_with_bounds m Cdetect)
    let Csource := Classical.choose (exists_preparedModularCanonicalDetector_prepared_source m Cdetect)
    let _Cresource := Classical.choose (exists_preparedModularCanonicalDetector_resource_budget
      (preparedModularCanonicalDetectorConstants m))
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → 0 ≤ P → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (Palloc + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let coarseTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let τ := Real.exp (-Pphysical)
      let Rspatial := spatialPrimitiveEnvelope Pphysical coarseTarget 0
      let ξLog := 2 * (Rspatial + spatialTupleToleranceLog Rspatial) + 4
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let sourceBudget := (Palloc + Csource) ^ Csource
      let budget := (P + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ sourceBudget ≤ budget ∧
      (preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) sourceBudget).nativeBudget ∈ Set.Icc 0 budget ∧
      (preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) sourceBudget).required ∈ Set.Icc 0 budget ∧
      Palloc ≤ sourceBudget ∧ Pearly ∈ Set.Icc 0 sourceBudget ∧
      Pphysical ∈ Set.Icc 0 sourceBudget ∧ coarseTarget ∈ Set.Icc 0 sourceBudget ∧
      ξLog ∈ Set.Icc 0 sourceBudget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ sourceBudget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 sourceBudget ∧ pDetect ∈ Set.Icc 0 sourceBudget ∧
        gainLog ∈ Set.Icc 0 sourceBudget ∧ target ∈ Set.Icc 0 sourceBudget ∧
        aDetect ∈ Set.Icc 0 sourceBudget ∧ D ∈ Set.Icc 0 sourceBudget ∧ Pk ∈ Set.Icc 0 sourceBudget ∧
        Prho ∈ Set.Icc 0 sourceBudget ∧ Ptail ∈ Set.Icc 0 sourceBudget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 sourceBudget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp sourceBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < t)
              (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              (Vtail : Fin m → ℝ≥0),
              PreparedModularCanonicalDetectorConstructedInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (hb := hb) (o := o) Palloc Qstride sourceBudget gainLog Pphysical) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  intro Cdetect Aalloc Aearly Cgeom Csource Cresource
  obtain ⟨_, _, hsource⟩ := exists_preparedModularCanonicalDetector_initial_source m Cdetect
  obtain ⟨C, hC, hcompose⟩ := exists_shiftedPower_triple_composition_budget Aalloc Csource Cresource
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Jalloc pnum P pSlice u Qstride hm hP hM hpSlice hu hQstride hnX
    Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D gainLog Pk
    Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K sourceBudget budget
  obtain ⟨hPalloc, hnum, _hSourceBudget, hAllocMaster, hEarlyMaster, hPhysicalMaster,
      hCoarseMaster, hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
      pRadius, R, hpRadius, hpRadiusMaster, hR, hModelMaster, hDetectMaster,
      hGainMaster, hTargetMaster, haMaster, hDMaster, hPkMaster, hPrhoMaster,
      hPtailMaster, t, ht, htone, hsampler⟩ :=
    hsource L hCoord hm hP hM hpSlice hu hQstride hnX
  have hSourceMaster : 0 ≤ sourceBudget := hP.trans (hPalloc.trans hAllocMaster)
  have hResourceUpper : (sourceBudget + Cresource) ^ Cresource ≤ budget := hcompose hP
  have hResourceConstant : 2 ≤ Cresource :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_resource_budget
      (preparedModularCanonicalDetectorConstants m))).1
  have hbudget : sourceBudget ≤ budget := by
    have hbase : 1 ≤ sourceBudget + Cresource := by
      have hcast : (2 : ℝ) ≤ Cresource := Nat.cast_le.mpr hResourceConstant
      linarith only [hSourceMaster, hcast]
    exact ((le_add_of_nonneg_right (Nat.cast_nonneg Cresource)).trans
      (le_self_pow₀ hbase (by omega))).trans hResourceUpper
  have hresources := (Classical.choose_spec (exists_preparedModularCanonicalDetector_resource_budget
    (preparedModularCanonicalDetectorConstants m))).2 sourceBudget hSourceMaster
  refine ⟨hPalloc, hnum, hbudget,
    ⟨hresources.1.nativeBudget.1, hresources.1.nativeBudget.2.trans hResourceUpper⟩,
    ⟨hresources.1.required.1, hresources.1.required.2.trans hResourceUpper⟩,
    hAllocMaster, hEarlyMaster, hPhysicalMaster,
    hCoarseMaster, hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
    pRadius, R, hpRadius, hpRadiusMaster, hR, hModelMaster, hDetectMaster,
    hGainMaster, hTargetMaster, haMaster, hDMaster, hPkMaster, hPrhoMaster,
    hPtailMaster, t, ht, htone, ?_⟩
  intro J _ U basis Pscale
  obtain ⟨S, hScaleMaster, hPkScale, hSMaster, ⟨geometry⟩, hgainKernel⟩ := hsampler U basis
  refine ⟨S, hScaleMaster, hPkScale, hSMaster, ?_, hgainKernel⟩
  intro hRpos hσpos stride N _ Q _ hb o bW _ ν _ _ _ _ _ μ _ _ _ _ _ μrows _ _ _ _ Vtail
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff
  have hAlloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hMaster : 0 ≤ sourceBudget := hAlloc0.trans hAllocMaster
  have hPMaster : P ≤ sourceBudget := hPalloc.trans hAllocMaster
  have hExpMaster : Real.exp Palloc ≤ Real.exp sourceBudget := Real.exp_le_exp.mpr hAllocMaster
  obtain ⟨_, hSliceModel, _, hSliceLog, _, hCtail, _, hcountModel, _, _, _, _, _, hα, _, _⟩ :=
    preparedModularCanonicalDetector_early_cap L Jalloc A hCoord hAlloc0 hnum hpSlice.1 hu.1
      R Vtail hRpos (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
  have hMk := (hgainKernel _ hα).2
  have hMkPk : (allocatedDetectedZeroKernelCutoff G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect
      (allocatedModelUnitThreshold u pModel
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B)))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))) : ℝ)
      ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr hPkScale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp sourceBudget := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hpRadiusMaster
  have hAearly : 2 ≤ Aearly :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorEarlyParameters m Cdetect)).1
  have hQearly0 : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  have hAllocQ : Palloc ≤ Qearly := by
    have hbase : 1 ≤ Palloc + Aearly := by
      have hcast : (2 : ℝ) ≤ Aearly := Nat.cast_le.mpr hAearly
      linarith only [hAlloc0, hcast]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Aearly)).trans
      (le_self_pow₀ hbase (by omega))
  have hQPhysical : Qearly ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX]
  have hDimPhysical : 2 ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hXPhysical : (nX : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hPkPhysical : Pk ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hQstridePhysical : Qstride ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions L Jalloc hCoord).1).trans
      (hnum.trans (hAllocQ.trans hQPhysical))
  have consumer := preparedModularCanonicalDetectorBudgetedInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    Palloc D target Pk Prho Qstride sourceBudget gainLog Pphysical
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer hMaster hDMaster.2 hPkMaster
    ⟨hQstride.1, hQstride.2.trans hPMaster⟩ hDetectMaster (hnX.trans hPMaster)
    (fun j => (hR j).2.1)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleMaster.2))
    hSMaster hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk hstride hstrideBound
    Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual
    (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (fun j i => enlargedPreparedCommonSamplerBlock_uniform L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    ⟨hu.1, hu.2.trans hPMaster⟩ hModelMaster hSliceModel hSliceLog hCtail hcountModel
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster.2 hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision.le hXiMaster.2
  intro r coarseTarget' τ' hτSpatial W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases hbases hξn hmass htotal Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hbox hdense hcount hcomplexity hnorm budget' hξone
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass htotal
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hbox hdense hcount hcomplexity hnorm
    (enlargedPreparedCommonKernel_analytic_capacity m Jalloc 0 (Nat.zero_le m)) hMk.2 hξone

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (0 + 1))))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
local notation "α" => allocatedModelUnitThreshold u pModel Kslice Ctail
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (0 + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

def PreparedModularCanonicalDetectorPositiveInterface
    (Pchart Qstride Pmaster pGain Pphysical : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    let r := preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) Pmaster
    let coarseTarget := pGain + 32
    let τ := Real.exp (-Pphysical)
    let hτSpatial := Real.exp_pos (-Pphysical)
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let ξn := normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α)
      Pphysical coarseTarget
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp r.required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp r.required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let hξn := normalizedTupleNarrowWidth_pos (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (_hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX) poly hmem N
      hN hW hτSpatial hξn stride cells hmass bases hbases hnormalizer.2.2.1
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    ∀ {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
      {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)] [∀ z j, LieAlgebra ℚ (Ldetect z j)]
      {dims : ∀ z, Tests z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) 0 (dims z j))
      (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
      (slices : ∀ z, Tests z → Finset Sites)
      (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
      (stepdetect : ∀ z, Tests z → ℕ)
      (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < stepdetect z j) →
    (∀ z j, (slices z j).image e = commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j)) →
    (∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) pSlice ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let budget := r.nativeBudget
    let hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect qDetect α) Pphysical coarseTarget
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial
      hξone N hN
      hmargin e hrootSum
    ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Qmodel : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Qmodel i ∈ twistedNativeSampleFunctions (fun _ : Fin nX => 1) 0 budget
        (fun t : integerBox N => t.val)
        (fun (twist : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
            (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩)
          (t : integerBox N) => twist.eval N poly t.val)) ∧
      input = (∑ i, coeff i • Qmodel i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
      sampledSliceSeminorm pathLaw physical slices
        (fun z j t => star ((Vdetect z j).eval
          (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) err ≤ Real.exp (-u) ∧
      (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30)

end Consumer

theorem exists_preparedModularCanonicalDetector_positive (m : ℕ) (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Aearly := Classical.choose (exists_preparedModularCanonicalDetectorEarlyParameters m Cdetect)
    let _Cgeom := Classical.choose (exists_detected_canonical_native_source_with_bounds m Cdetect)
    let Csource := Classical.choose (exists_preparedModularCanonicalDetector_prepared_source m Cdetect)
    let _Cresource := Classical.choose (exists_preparedModularCanonicalDetector_resource_budget
      (preparedModularCanonicalDetectorConstants m))
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → 0 ≤ P → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (Palloc + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let coarseTarget := gainLog + 32
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let τ := Real.exp (-Pphysical)
      let Rspatial := spatialPrimitiveEnvelope Pphysical coarseTarget 0
      let ξLog := 2 * (Rspatial + spatialTupleToleranceLog Rspatial) + 4
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let sourceBudget := (Palloc + Csource) ^ Csource
      let budget := (P + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ sourceBudget ≤ budget ∧
      (preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) sourceBudget).nativeBudget ∈ Set.Icc 0 budget ∧
      (preparedModularCanonicalDetectorResources (preparedModularCanonicalDetectorConstants m) sourceBudget).required ∈ Set.Icc 0 budget ∧
      Palloc ≤ sourceBudget ∧ Pearly ∈ Set.Icc 0 sourceBudget ∧
      Pphysical ∈ Set.Icc 0 sourceBudget ∧ coarseTarget ∈ Set.Icc 0 sourceBudget ∧
      ξLog ∈ Set.Icc 0 sourceBudget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ sourceBudget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 sourceBudget ∧ pDetect ∈ Set.Icc 0 sourceBudget ∧
        gainLog ∈ Set.Icc 0 sourceBudget ∧ target ∈ Set.Icc 0 sourceBudget ∧
        aDetect ∈ Set.Icc 0 sourceBudget ∧ D ∈ Set.Icc 0 sourceBudget ∧ Pk ∈ Set.Icc 0 sourceBudget ∧
        Prho ∈ Set.Icc 0 sourceBudget ∧ Ptail ∈ Set.Icc 0 sourceBudget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 sourceBudget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp sourceBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < t)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              (Vtail : Fin m → ℝ≥0),
              PreparedModularCanonicalDetectorPositiveInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (hb := hb) (o := o) Palloc Qstride sourceBudget gainLog Pphysical) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  intro Cdetect Aalloc Aearly Cgeom Csource Cresource
  obtain ⟨_, _, hsource⟩ := exists_preparedModularCanonicalDetector_initial_source m Cdetect
  obtain ⟨C, hC, hcompose⟩ := exists_shiftedPower_triple_composition_budget Aalloc Csource Cresource
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Jalloc pnum P pSlice u Qstride hm hP hM hpSlice hu hQstride hnX
    Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D gainLog Pk
    Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K sourceBudget budget
  obtain ⟨hPalloc, hnum, _hSourceBudget, hAllocMaster, hEarlyMaster, hPhysicalMaster,
      hCoarseMaster, hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
      pRadius, R, hpRadius, hpRadiusMaster, hR, hModelMaster, hDetectMaster,
      hGainMaster, hTargetMaster, haMaster, hDMaster, hPkMaster, hPrhoMaster,
      hPtailMaster, t, ht, htone, hsampler⟩ :=
    hsource L hCoord hm hP hM hpSlice hu hQstride hnX
  have hSourceMaster : 0 ≤ sourceBudget := hP.trans (hPalloc.trans hAllocMaster)
  have hResourceUpper : (sourceBudget + Cresource) ^ Cresource ≤ budget := hcompose hP
  have hResourceConstant : 2 ≤ Cresource :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetector_resource_budget
      (preparedModularCanonicalDetectorConstants m))).1
  have hbudget : sourceBudget ≤ budget := by
    have hbase : 1 ≤ sourceBudget + Cresource := by
      have hcast : (2 : ℝ) ≤ Cresource := Nat.cast_le.mpr hResourceConstant
      linarith only [hSourceMaster, hcast]
    exact ((le_add_of_nonneg_right (Nat.cast_nonneg Cresource)).trans
      (le_self_pow₀ hbase (by omega))).trans hResourceUpper
  have hresources := (Classical.choose_spec (exists_preparedModularCanonicalDetector_resource_budget
    (preparedModularCanonicalDetectorConstants m))).2 sourceBudget hSourceMaster
  refine ⟨hPalloc, hnum, hbudget,
    ⟨hresources.1.nativeBudget.1, hresources.1.nativeBudget.2.trans hResourceUpper⟩,
    ⟨hresources.1.required.1, hresources.1.required.2.trans hResourceUpper⟩,
    hAllocMaster, hEarlyMaster, hPhysicalMaster,
    hCoarseMaster, hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
    pRadius, R, hpRadius, hpRadiusMaster, hR, hModelMaster, hDetectMaster,
    hGainMaster, hTargetMaster, haMaster, hDMaster, hPkMaster, hPrhoMaster,
    hPtailMaster, t, ht, htone, ?_⟩
  intro J _ U basis Pscale
  obtain ⟨S, hScaleMaster, hPkScale, hSMaster, ⟨geometry⟩, hgainKernel⟩ := hsampler U basis
  refine ⟨S, hScaleMaster, hPkScale, hSMaster, ?_, hgainKernel⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ _ _ _ _ _ μrows _ _ _ _ Vtail
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff
  have hAlloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hMaster : 0 ≤ sourceBudget := hAlloc0.trans hAllocMaster
  have hPMaster : P ≤ sourceBudget := hPalloc.trans hAllocMaster
  have hExpMaster : Real.exp Palloc ≤ Real.exp sourceBudget := Real.exp_le_exp.mpr hAllocMaster
  obtain ⟨_, hSliceModel, _, hSliceLog, _, hCtail, _, hcountModel, _, _, _, _, _, hα, _, _⟩ :=
    preparedModularCanonicalDetector_early_cap L Jalloc A hCoord hAlloc0 hnum hpSlice.1 hu.1
      R Vtail hRpos (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
  have hMk := (hgainKernel _ hα).2
  have hMkPk : (allocatedDetectedZeroKernelCutoff G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect
      (allocatedModelUnitThreshold u pModel
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B)))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))) : ℝ)
      ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr hPkScale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp sourceBudget := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hpRadiusMaster
  have hAearly : 2 ≤ Aearly :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorEarlyParameters m Cdetect)).1
  have hQearly0 : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  have hAllocQ : Palloc ≤ Qearly := by
    have hbase : 1 ≤ Palloc + Aearly := by
      have hcast : (2 : ℝ) ≤ Aearly := Nat.cast_le.mpr hAearly
      linarith only [hAlloc0, hcast]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Aearly)).trans
      (le_self_pow₀ hbase (by omega))
  have hQPhysical : Qearly ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX]
  have hDimPhysical : 2 ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hXPhysical : (nX : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hPkPhysical : Pk ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hQstridePhysical : Qstride ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkMaster.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions L Jalloc hCoord).1).trans
      (hnum.trans (hAllocQ.trans hQPhysical))
  intro r coarseTarget' τ' hτSpatial W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases hξn Z
  have hτInvMaster : τ'⁻¹ ≤ Real.exp sourceBudget := by
    rw [← one_div, hτinv]
    exact Real.exp_le_exp.mpr hPhysicalMaster.2
  have hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect (allocatedModelUnitThreshold u pModel
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B)))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))))
    Pphysical coarseTarget
  have hξInvMaster : ξn⁻¹ ≤ Real.exp sourceBudget :=
    (preparedModularDetector_narrow_width B selection hPhysicalMaster.1 hCoarseMaster.1
      (hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)) hDimPhysical hvarsPhysical hXPhysical).2.trans
      (Real.exp_le_exp.mpr hXiMaster.2)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularCanonicalDetector_positive_bounds B U basis S hb o μ ν hRpos hσpos
      (fun _ => htone) Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 hMaster geometry.hdimensions
      hDMaster.2 (hnX.trans hPMaster)
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleMaster.2)) hSMaster
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr (hQstride.2.trans hPMaster)))
      hτSpatial hτInvMaster hτhalf hτdim hξn hξone hξInvMaster
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have consumer := preparedModularCanonicalDetectorBudgetedInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    Palloc D target Pk Prho Qstride sourceBudget gainLog Pphysical
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer hMaster hDMaster.2 hPkMaster
    ⟨hQstride.1, hQstride.2.trans hPMaster⟩ hDetectMaster (hnX.trans hPMaster)
    (fun j => (hR j).2.1)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleMaster.2))
    hSMaster hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk hstride hstrideBound
    Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual
    (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (fun j i => enlargedPreparedCommonSamplerBlock_uniform L Jalloc 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    ⟨hu.1, hu.2.trans hPMaster⟩ hModelMaster hSliceModel hSliceLog hCtail hcountModel
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster.2 hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision.le hXiMaster.2
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm
    budget' hξone'
  obtain ⟨_, hmodels⟩ := completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm (enlargedPreparedCommonKernel_analytic_capacity m Jalloc 0 (Nat.zero_le m))
    hMk.2 hξone'
  exact hmodels

end Erdos3.VectorPolynomial

end

end OAI
