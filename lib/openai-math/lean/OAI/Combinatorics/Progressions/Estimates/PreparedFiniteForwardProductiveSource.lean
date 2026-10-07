import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalProductiveSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteScheduleProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0)

    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    {K : Type} [Fintype K] (degree Cdetect : K → ℕ) (kModel : K)
    (hdegree : ∀ k, degree k ≤ m) (hdegreeZero : degree kModel = 0)
    (hCzero : Cdetect kModel = sampledSupportedSlicedDetectionConstant 0 Pdetect)
    (Bstruct Qstride u p forecastCap : ℝ)
    (sourceU modelLog sliceLog : K → ℝ)
    (hModelSource : sourceU kModel = u + 2 * p + 1)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ Real.exp (modelLog k))
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) + Qstride + ∑ k, Pk k
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog Pphysical
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount m (nX + m * M)) * (nX + m * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := preparedFiniteScheduleDirectMaster Bstruct D pRadius Qstride Pphysical sourceU modelLog Prho target detectionGain
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    sliceLog kModel * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
        (detectionGain k) Pphysical coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, Cdetect k = sampledSupportedSlicedDetectionConstant (degree k) Pdetect →
        PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride Pmaster Plate (detectionGain k) Pphysical coarseTarget) ∧
      (∀ k, degree k = 0 →
        Cdetect k = sampledSupportedSlicedDetectionConstant 0 Pdetect →
        PreparedScheduledModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride Pmaster Plate (detectionGain k) Pphysical coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := m) (nX := nX) (M := M) (prep := prep) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride Pmaster Plate (detectionGain kModel) Pphysical coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  intro pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ hnum hWexp
    hSliceLog hCtail hForecastCap hForecastCapP
  have hpnum : 0 ≤ pnum := Nat.cast_nonneg _
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep (modularInitialBlockCount m (nX + m * M)) hCoord
  have hblocks (s : K) (a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)) :
      (boundedBooleanJetRows (Fin (degree s + 1)) (a.1.val + 1)).card ≤ Fintype.card ((EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (degree s + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets prep (modularInitialBlockCount m (nX + m * M)) (degree s) (hdegree s) a
  have hpDetect (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    linarith only [hsourceU k, hmodelLog k]
  have haDetect (k) : 0 ≤ aDetect k := by
    dsimp only [aDetect]
    linarith only [hsourceU k, hmodelLog k]
  have hgainDetect (k) : 0 ≤ detectionGain k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) _ (hpDetect k) (hpDetect k) (haDetect k)
  have hkernel (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgainDetect k
    have := hpDetect k
    positivity
  have hkernelSum : 0 ≤ ∑ k, Pk k := Finset.sum_nonneg (fun k _ => hkernel k)
  have hphysical : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    positivity
  have hphysicalX : (nX : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    have hcount : (0 : ℝ) ≤ Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) := Nat.cast_nonneg _
    have hm2 : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [hcount, hm2, hkernelSum, hQstride]
  have htarget (k) : 0 ≤ target k := by
    have he := coefficientErrorSpatialLog_nonneg hphysical
    dsimp only [target]
    linarith only [hgainDetect k, he]
  have hactual := exists_preparedFiniteScheduleGeometry m degree Cdetect (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) nX pDetect aDetect target
    hm hdegree hB ⟨hpnum, hnum⟩ (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j))
    (fun j => Nat.cast_le.mpr (hn j)) hblocks hpDetect haDetect hQstride htarget
  obtain ⟨hpRadius, hR, hD, hlogs, t, ht, hsamplers⟩ := hactual
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, hscales⟩ := hsamplers hQσ
  have hW : 1 ≤ W := (physicalBadProductGap_budget _
    (show 0 ≤ gainLog + 8 by linarith only [hg]) hVlog Qgood hQgood hQexp).1
  obtain ⟨S, hFloor, hS, hgap, hGeometryAll⟩ := hscales Lmin hW hQw hWexp hPmin hLmin U b
  let σ := preparedUniformDegreeTolerance t Qσ
  have hF (s) : 0 ≤ pDetect s + 2 := by linarith only [hpDetect s]
  have hTmod (s) : 0 ≤ Tmod s :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlogs s).2.1)
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hLengths (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD hPscale (hlogs s).2.2.1 (hlogs s).2.1
      (htarget s) (hF s) (hTmod s)).2.2.1
  have hPseed : 0 ≤ Pseed := allocatedScaleLog_nonneg
    (add_nonneg (add_nonneg (add_nonneg hPscale (Finset.sum_nonneg (fun s _ => hLengths s))) hPmin)
      (by norm_num))
  have scalarAll := preparedFiniteScheduleDirectScalarBounds_explicit m degree Cdetect hdegree (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    nX (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) Bstruct D pRadius Qstride Pscale
    requestedCoarse (allocatedWitnessScaleLog Pseed Qw) sourceU modelLog sliceLog Prho
    hB hD hpRadius.1 hsourceU hmodelLog hQstride (fun k => (hlogs k).2.2.1)
    hsliceModel hcountModel hPkScale
  have scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride Pmaster Plate
      (detectionGain kModel) Pphysical coarseTarget pRadius (u + 2 * p + 1)
      (modelLog kModel) (sliceLog kModel) := by
    have hstage : PreparedUniformDegreeDirectScalarBounds m (degree kModel) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect kModel) Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel)
        Qstride Pmaster Plate (detectionGain kModel) Pphysical coarseTarget pRadius
        (sourceU kModel) (modelLog kModel) (sliceLog kModel) := scalarAll kModel
    rw [hdegreeZero, hCzero, hModelSource] at hstage
    exact hstage
  have hGeometryZero : PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride
      (allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel)) pRadius
      (2 * (u + 2 * p + 1) + 4 * modelLog kModel + 7) (detectionGain kModel) := by
    have hstage : PreparedUniformDegreeGeometryAt
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
        U b S (degree kModel) (Cdetect kModel) nX
        Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride
        (pDetect kModel) pRadius (aDetect kModel) (detectionGain kModel) := hGeometryAll kModel
    have hpd : pDetect kModel = allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel) := by
      change allocatedModelTestLog (sourceU kModel) (modelLog kModel) = _
      rw [hModelSource]
    have had : aDetect kModel = 2 * (u + 2 * p + 1) + 4 * modelLog kModel + 7 := by
      change 2 * sourceU kModel + 4 * modelLog kModel + 7 = _
      rw [hModelSource]
    rw [hdegreeZero, hCzero, hpd, had] at hstage
    exact hstage
  have hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hentry (k) : 0 ≤ sourceU k + modelLog k + pDetect k + Prho k + target k + detectionGain k + 32 := by
    have hr := (hlogs k).2.2.1
    linarith only [hsourceU k, hmodelLog k, hpDetect k, hr, htarget k, hgainDetect k]
  have htotal := Finset.single_le_sum (fun k _ => hentry k) (Finset.mem_univ kModel)
  have hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster := by
    have hr := (hlogs kModel).2.2.1
    change gainLog + (nX : ℝ) + 8 ≤ Bstruct + D + pRadius + Qstride + Pphysical +
      ∑ k, (sourceU k + modelLog k + pDetect k + Prho k + target k + detectionGain k + 32)
    linarith only [hgChart, hD, hpRadius.1, hQstride, hphysicalX, htotal,
      hsourceU kModel, hmodelLog kModel, hpDetect kModel, hr, htarget kModel, hgainDetect kModel]
  refine ⟨(fun j => (hR j).1), σ, hσ, S, hpRadius.1,
    (fun j => (hR j).2), hσone, hσexp, hσinv, hFloor, hS, hgap, hGeometryAll, scalarAll, ?_, ?_, ?_⟩
  · intro k hconstant
    exact preparedFiniteScheduleGeometryDirectSource
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
      (Cdetect k) hconstant (hdegree k)
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
      (detectionGain k) Pphysical coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
  · intro k hzero hconstant
    exact preparedFiniteScheduleGeometryModel
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
      (degree k) (Cdetect k) hzero hconstant
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
      (detectionGain k) Pphysical coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
  · exact preparedUniformDegreeProductiveSource
      (prep := prep) (U := U) (b := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride Pmaster Plate (detectionGain kModel)
      Pphysical coarseTarget pRadius scalar hGeometryZero
      (fun j => (hR j).2.1) (fun j => (hR j).2.2)
      hu hp hSliceLog hCtail hForecastCap hForecastCapP
      Qgood hm hnX hCoord hpRadius.1 hPseed hQw hVlog hg hQgood hQexp
      hWitnessLate hgain hB hnChart hgChart hGainMaster rfl hS hgap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteForwardProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0)

    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (depth A : ℕ) (stageCountConstant : ℕ → ℕ)
    (hdepth : depth ≤ m) (hA : 2 ≤ A)
    (Bstruct Qstride forecastCap stageLog : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let K := PreparedFiniteForwardSlot depth
    let degree : K → ℕ := preparedFiniteForwardSlotDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteForwardModelSlot 0
    let sourceU := fun k : K =>
      preparedFiniteForwardSourcePrecision A stageCountConstant k.1.val Bstruct gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant k.1.val Bstruct
    let sliceLog := fun k : K => preparedFiniteForwardParameter A stageCountConstant k.1.val Bstruct
    let u := preparedFiniteForwardModelPrecision A stageCountConstant 0 Bstruct gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant 0 Bstruct
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) + Qstride + ∑ k, Pk k
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog Pphysical
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount m (nX + m * M)) * (nX + m * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := preparedFiniteScheduleDirectMaster Bstruct D pRadius Qstride Pphysical sourceU modelLog Prho target detectionGain
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
        (detectionGain k) Pphysical coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (preparedFiniteForwardSlot_degree_le hdepth k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride Pmaster Plate (detectionGain k) Pphysical coarseTarget) ∧
      (∀ n : Fin (depth + 1),
        let k : K := preparedFiniteForwardModelSlot n
        PreparedScheduledModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride Pmaster Plate (detectionGain k) Pphysical coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := m) (nX := nX) (M := M) (prep := prep) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride Pmaster Plate (detectionGain kModel) Pphysical coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  intro K degree Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ hnum hWexp
    hCtail hForecastCap hForecastCapP
  have hcount : (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ)
      ≤ Bstruct :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions prep
      (modularInitialBlockCount m (nX + m * M)) hCoord).1).trans hnum
  obtain ⟨hdegree, hsourceU, hmodelLog, hsliceModel, hcountModel, hmodels⟩ :=
    preparedFiniteForwardSourceSlots_inputs depth m A
      (Fintype.card (LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      stageCountConstant hdepth hA hB ⟨hg, hgChart⟩ hstage hcount
  have hModelSource : sourceU kModel = u + 2 * p + 1 := (hmodels 0).1
  have hSliceLog : sliceLog kModel * Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p :=
    (hmodels 0).2
  have hu : 0 ≤ u :=
    (preparedFiniteForward_model_precision_bounds A stageCountConstant 0 hB
      ⟨hg, hgChart⟩ hstage).1
  have hp : 0 ≤ p := hmodelLog kModel
  have original := exists_preparedFiniteScheduleProductiveSource
    (m := m) (nX := nX) (M := M) prep U b stride N Pdetect Vtail
    Q hb o bW ν μ μrows degree Cdetect kModel hdegree rfl rfl
    Bstruct Qstride u p forecastCap sourceU modelLog sliceLog hModelSource
    Qσ Qw Pmin requestedCoarse gainLog gain Vlog Lmin Qgood hm hnX hCoord
    hB hu hp hsourceU hmodelLog hsliceModel hcountModel hQstride hQσ hQw hPmin hLmin
    hg hVlog hQgood hQexp hgain hnChart hgChart
  obtain ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, hdirect, hmodel, hproductive⟩ :=
    original hnum hWexp hSliceLog hCtail hForecastCap hForecastCapP
  refine ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, ?_, ?_, hproductive⟩
  · intro k
    exact hdirect k rfl
  · intro n
    exact hmodel (preparedFiniteForwardModelSlot n) rfl rfl

end Erdos3.VectorPolynomial

end

end OAI
