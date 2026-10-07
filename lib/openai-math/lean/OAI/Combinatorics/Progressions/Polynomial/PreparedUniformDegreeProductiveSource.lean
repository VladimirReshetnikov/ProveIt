import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSourceModel
import OAI.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastProductiveModelAttachment

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

def preparedUniformDegreeProductiveCertificateBudget
    (M nX : ℕ) (pRadius Pscale Pseed Qw Elog Vlog : ℝ) : ℝ :=
  1 + (M : ℝ) + (nX : ℝ) + pRadius + Pscale + Pseed + Qw + Elog + Vlog

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedUniformDegreeProductiveSourceCertificate
    {pRadius Pscale Pseed Qw Elog Vlog : ℝ} (Qbad : ℕ)
    (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQbad : 1 ≤ Qbad) (hQexp : (Qbad : ℝ) ≤ Real.exp Vlog)
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          Elog Vlog Qbad ≤
          (layerSamplerGapWidth
            (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
            R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    ∀ Bcert : ℝ,
      preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw Elog Vlog ≤ Bcert →
      PreparedShortCertifiedSameScaleBadProductInterface prep U b S Bcert Elog Vlog Qbad := by
  intro Bcert hcert
  unfold preparedUniformDegreeProductiveCertificateBudget at hcert
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hnX : 0 ≤ (nX : ℝ) := Nat.cast_nonneg nX
  have hB : 1 ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hQw, hElog, hVlog]
  have hMB : (M : ℝ) ≤ Bcert := by linarith only [hcert, hnX, hpRadius, hPscale, hPseed, hQw, hElog, hVlog]
  have hnXB : (nX : ℝ) ≤ Bcert := by linarith only [hcert, hM, hpRadius, hPscale, hPseed, hQw, hElog, hVlog]
  have hRadiusB : pRadius ≤ Bcert := by linarith only [hcert, hM, hnX, hPscale, hPseed, hQw, hElog, hVlog]
  have hScaleB : Pscale ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPseed, hQw, hElog, hVlog]
  have hSeedB : Pseed ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hQw, hElog, hVlog]
  have hQwB : Qw ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hElog, hVlog]
  have hEB : Elog ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hQw, hVlog]
  have hVB : Vlog ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hQw, hElog]
  apply preparedShortCertifiedSameScaleBadProductInterface_of_bounds prep U b S Qbad
    hB hMB hnXB ⟨hElog, hEB⟩ ⟨hVlog, hVB⟩ hQbad hQexp hm hCoord
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hRadiusB))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hScaleB))
  · exact hS.trans (Real.exp_le_exp.mpr
      (allocatedWitnessScaleLog_le_prepared_envelope (zero_le_one.trans hB)
        ⟨hPseed, hSeedB⟩ ⟨hQw, hQwB⟩ hElog hVlog))
  · exact hprincipal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedUniformDegreeProductiveSourceRawBounds
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    {Pchart Qstride Pmaster Plate Pphysical coarseTarget pRadius Pscale Pseed Qw
      gainLog gain Vlog D target Pk Prho : ℝ} (Qgood : ℕ)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (s := 0) (nX := nX)
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog uSource pModel)
      (Real.toNNReal (Real.exp pRadius)))
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hVlog : 0 ≤ Vlog) (hg : 0 ≤ gainLog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hD : D ≤ Pmaster) (hnMaster : (nX : ℝ) ≤ Pmaster)
    (hRadiusMaster : pRadius ≤ Pmaster) (hScaleLate : Pscale ≤ Plate)
    (hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate)
    (hStrideMaster : Qstride ≤ Pmaster) (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hchart : 0 ≤ Pchart) (hnChart : (nX : ℝ) ≤ Pchart)
    (hgChart : gainLog ≤ Pchart)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          (gainLog + 8) Vlog Qgood ≤
          (layerSamplerGapWidth
            (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
            R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hξLate : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate) :
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget
      M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    PreparedShortForecastSourceRawBounds prep U b S selection Pdetect uSource pModel pSlice
      Vtail u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D ∧ Plate ≤ Pwidth := by
  intro baseB0 Pwidth
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLateWidth : Plate ≤ Pwidth := by
    dsimp only [Pwidth]
    nlinarith only [sq_nonneg Plate]
  have hRi (j) : (R j)⁻¹ ≤ Real.exp pRadius := by
    have h := geometry.hK j
    simpa only [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos pRadius).le] using h
  have hcert := preparedUniformDegreeProductiveSourceCertificate prep U b S Qgood
    hpRadius geometry.hP hPseed hQw (by linarith only [hg]) hVlog hQgood hQexp hm hCoord
    hRi geometry.hσi hS hprincipal
  refine ⟨{
    hcert := hcert
    hnX := hnX
    hσ1 := fun j => (geometry.hσsmall j).trans geometry.htone
    hsmall := fun C hC hCB => (geometry.hbudgets C hC hCB).1
    hMaster := hMaster
    hLate := hLate
    hd := geometry.hdimensions
    hD := hD
    hnMaster := hnMaster
    hRi := fun j => (hRi j).trans (Real.exp_le_exp.mpr hRadiusMaster)
    hσi := fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleLate)
    hS := hS.trans (Real.exp_le_exp.mpr hWitnessLate)
    hprojection := le_rfl
    hVlog := hVlog
    hQexp := hQexp
    hg := hg
    hgain := hgain
    hstrideWidth := hStrideMaster.trans (hLate.trans hLateWidth)
    hτWidth := hPhysicalMaster.trans (hLate.trans hLateWidth)
    hξWidth := hξLate.trans (Real.exp_le_exp.mpr hLateWidth)
    hbase := ?_
    hchart := hchart
    hwidth := hPlate.trans hLateWidth
    hnChart := hnChart
    hgChart := hgChart }, hLateWidth⟩
  dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
  have hPscale := geometry.hP
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedUniformDegreeProductiveSourceConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius Pscale
      Pseed Qw gainLog gain Vlog : ℝ) (Qgood : ℕ) : Prop :=
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget
      M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
      (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) (Q := Q) (R := R) (σ := σ) prep U b hR hσ S (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m)) stride N Pdetect
      (u + 2 * p + 1) pModel pSlice Vtail τ u p forecastCap hb o bW μ
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      Bcert gainLog gain Pgood Qgood (preparedSpatialKernelBlocks m M nX) Pwidth

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedUniformDegreeProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius (u + 2 * p + 1) pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt (m := m) («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (u + 2 * p + 1) pModel) pRadius
      (2 * (u + 2 * p + 1) + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p)
    (hCtail : (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p)
    {Pseed Qw Vlog gainLog gain : ℝ} (Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hVlog : 0 ≤ Vlog) (hg : 0 ≤ gainLog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hchart : 0 ≤ Pchart) (hnChart : (nX : ℝ) ≤ Pchart)
    (hgChart : gainLog ≤ Pchart) (hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster)
    (hτeq : τ = Real.exp (-(gainLog + (nX : ℝ) + 8)))
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          (gainLog + 8) Vlog Qgood ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedUniformDegreeProductiveSourceConclusion
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius Pscale
      Pseed Qw gainLog gain Vlog Qgood := by
  classical
  unfold PreparedUniformDegreeProductiveSourceConclusion
  intro baseB0 Pwidth Bcert Pgood
  obtain ⟨geometry⟩ := geometryAt.1
  have hσone (j) : σ j ≤ 1 := (geometry.hσsmall j).trans geometry.htone
  have hSLate := hS.trans (Real.exp_le_exp.mpr hWitnessLate)
  obtain ⟨hModel, hξLate⟩ := preparedUniformDegreeGeometryModel
    («B» := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    («selection» := (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))) (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := pModel)
    (pSlice := pSlice) (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate
    (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep (modularInitialBlockCount m (nX + m * M)) 0
      (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep (modularInitialBlockCount m (nX + m * M)) 0
      (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (enlargedPreparedCommonKernel_analytic_capacity m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
    hu hp hSliceLog hCtail hForecastCap hForecastCapP
  obtain ⟨hRaw, hLateWidth⟩ := preparedUniformDegreeProductiveSourceRawBounds
    prep U b S (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m)) Pdetect (u + 2 * p + 1) pModel pSlice Vtail u p forecastCap Qgood geometry
    hm hnX hCoord hpRadius hPseed hQw hVlog hg hQgood hQexp
    scalar.master_nonneg scalar.late scalar.dimension_master scalar.ambient_master
    scalar.radius_master scalar.scale_late hWitnessLate scalar.stride_master.2
    scalar.physical_master.2 hgain hchart hnChart hgChart hS hprincipal hξLate
  exact sharedWidthPreparedShortForecastProductiveModelAttachment
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    («selection» := (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))) (stride := stride) (N := N) (Pdetect := Pdetect)
    («uSource» := (u + 2 * p + 1)) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    baseB0 Vlog gainLog gain Pwidth Qgood (preparedSpatialKernelBlocks m M nX)
    (D := D) hRaw hLateWidth scalar.chart_master scalar.stride_master.2
    hGainMaster hτeq hξLate hModel

end Erdos3.VectorPolynomial

end

end OAI
