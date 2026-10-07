import OAI.Combinatorics.Progressions.Dynamics.PreparedModularGeneralUniformResourceBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorPositive
import OAI.Combinatorics.Progressions.Polynomial.PreparedPolynomialPhysicalBadProductSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedModularGeneralDetectorLateMaster
    (sourceBudget geometryBudget Qw Pphysical coarseTarget : ℝ) : ℝ :=
  sourceBudget + allocatedWitnessScaleLog geometryBudget Qw + coarseTarget +
    (2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4) + 1

theorem preparedModularGeneralDetectorLateMaster_bounds
    {sourceBudget geometryBudget Qw Pphysical coarseTarget : ℝ}
    (hsource : 0 ≤ sourceBudget) (hgeometry : 0 ≤ geometryBudget)
    (hQw : 0 ≤ Qw) (hphysical : 0 ≤ Pphysical) (hcoarse : 0 ≤ coarseTarget) :
    let Plate := preparedModularGeneralDetectorLateMaster
      sourceBudget geometryBudget Qw Pphysical coarseTarget
    0 ≤ Plate ∧ sourceBudget ≤ Plate ∧
      allocatedWitnessScaleLog geometryBudget Qw ≤ Plate ∧ coarseTarget ≤ Plate ∧
      (2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
        spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4) ≤ Plate := by
  have hwitness : 0 ≤ allocatedWitnessScaleLog geometryBudget Qw := by
    exact add_nonneg (allocatedScaleLog_nonneg hgeometry) (mul_nonneg (sq_nonneg _) hQw)
  have hR := (spatialPrimitiveEnvelope_bounds hphysical hcoarse (le_refl (0 : ℝ))).1
  have htuple := spatialTupleToleranceLog_nonneg hR
  dsimp only [preparedModularGeneralDetectorLateMaster]
  exact ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
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

def PreparedSameScaleBadProductInterface (B Elog Vlog : ℝ) (Q : ℕ) : Prop :=
  let Ps := (B + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m
  ∀ {E : Fin m → Type} [∀ j, Fintype (E j)]
    (_bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp B) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp B)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (_hρ : 0 < ρ) (_hρPs : 1 / ρ ≤ Real.exp B)
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hSmax : 0 ≤ Smax) (_hSmaxPs : Smax ≤ Real.exp B) (_hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (_hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (_hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (_hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (_hwide : ∀ z, ρ * H z.2 ≤ width z)
    , let Dphysical := fun z : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ =>
      allocatedCoefficientDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * (physicalBadProductAccuracy Elog Vlog) ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < (quantitativeBadPrimeRadius Elog) ∧ ((quantitativeBadPrimeRadius Elog) : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * (quantitativeBadPrimeRadius Elog)) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M)
                    (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) primes ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog)

theorem preparedSameScaleBadProductInterface_of_bounds
    {B Elog Vlog : ℝ} (Q : ℕ) (hB : 1 ≤ B) (hMB : (M : ℝ) ≤ B) (hnXB : (nX : ℝ) ≤ B)
    (hElogB : Elog ∈ Set.Icc 0 B) (hVlogB : Vlog ∈ Set.Icc 0 B)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp B) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp B)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog B (2 * B + 2 * Vlog + 5 * Elog + 24)))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedSameScaleBadProductInterface prep U b S B Elog Vlog Q := by
  unfold PreparedSameScaleBadProductInterface
  intro Ps E instE bW hb o C V hC hV hR hσ hσ1
    Cinv hCinv hchart hsmall hAP hCP hVP
    instLattice instCompact instMeasurable instBorel μ instLeft instProbability ν instνLeft instνProb
    poly hp hm ρ Rs Smax hρ hρPs stride hstride
    hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells width hwidth hwide
  let P := (B + preparedBadProductCoefficientExponent m) ^ preparedBadProductCoefficientExponent m
  have hbudget := (exists_preparedBadProductFinalBudget m).choose_spec.choose_spec
  obtain ⟨hP1, hPs1, hBP, hP0P, hprimitive, hPscale, hbudgetP, hframe, hPPS, hWlog, hfreq, hmass⟩ :=
    hbudget.2.2 hB hMB hnXB (show B ∈ Set.Icc 0 B from ⟨zero_le_one.trans hB, le_rfl⟩) hElogB hVlogB
  have hP : 0 ≤ P := zero_le_one.trans hP1
  have hPs : 0 ≤ Ps := zero_le_one.trans hPs1
  have hbudgetPs := hbudgetP.trans hPPS
  have hcounts : (((m + 1) * (enlargedPreparedCommonSamplerDimension m M
        (modularInitialBlockCount m (nX + m * M)) + 1) ^ m +
        enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)) : ℕ) : ℝ) ≤ P := by
    simpa only [P, preparedBadProductCoefficientExponent, Nat.cast_add] using hprimitive
  exact exists_prepared_enlarged_physical_bad_product prep U bW b hb o S C V hC hV Elog Vlog Q
    hElogB.1 hVlogB.1 hQ hQexp hmpos hCoord hR hσ hσ1 Cinv hCinv hchart hsmall hP hcounts
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hBP))
    (hAP.trans (Real.exp_le_exp.mpr hBP)) (hS.trans (Real.exp_le_exp.mpr hPscale))
    (fun j => (hCP j).trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hVP j).trans (Real.exp_le_exp.mpr hBP)) hbudgetP μ ν poly hp hm
    hPs hframe hbudgetPs hρ (hρPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) stride hstride
    hSmax (hSmaxPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) hstrideMax
    H hsize hrank hRs cells hcells width hwidth hwide hfreq hmass hprincipal hPPS hWlog

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
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
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

def PreparedModularGeneralDetectorInterface
    (Pchart Qstride Pmaster Plate _pGain Pphysical coarseTarget : ℝ) : Prop :=
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
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let τ := Real.exp (-Pphysical)
    let hτSpatial := Real.exp_pos (-Pphysical)
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let ξn := normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α)
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
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
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
      (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) s (dims z j))
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
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
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
      (∀ i, Qmodel i ∈ twistedNativeSampleFunctions (fun _ : Fin nX => 1) s budget
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

theorem exists_preparedModularGeneralDetector (m s : ℕ) (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Cresource := Classical.choose (exists_preparedModularGeneral_uniform_resource_budget m)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect)
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    let Cphysical := Classical.choose (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
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
      let geometryBudget := (Palloc + Eextra + Cgeom) ^ Cgeom
      let sourceBudget := (Palloc + Cphysical) ^ Cphysical
      let totalBudget := (P + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ geometryBudget ≤ sourceBudget ∧ sourceBudget ≤ totalBudget ∧
      Pphysical ∈ Set.Icc 0 sourceBudget ∧ coarseTarget ∈ Set.Icc 0 sourceBudget ∧
      ξLog ∈ Set.Icc 0 sourceBudget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      (s + 1) * (s + 3) ≤ Fintype.card G ∧
      (∀ h : ℕ, h ≤ m → h * Jalloc ≤ Fintype.card G) ∧
      (∀ a : LayerSamplerAxis I n, Jalloc ≤ Fintype.card (B a)) ∧
      (∀ a : LayerSamplerAxis I n, (rowSets a.1).card ≤ Fintype.card (B a)) ∧
      (∀ i, (selection i).val = i.val) ∧
      (∀ inactive : LayerSamplerAxis I n → Prop,
        (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) I inactive j)) ≤
          nX + m * M) ∧
      ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
        modularRankSmallBallExponent m⌉₊ ≤ Jalloc ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ geometryBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      pModel ∈ Set.Icc 0 geometryBudget ∧ pDetect ∈ Set.Icc 0 geometryBudget ∧
      aDetect ∈ Set.Icc 0 geometryBudget ∧ target ∈ Set.Icc 0 geometryBudget ∧
      D ∈ Set.Icc 0 geometryBudget ∧ gainLog ∈ Set.Icc 0 geometryBudget ∧
      Pk ∈ Set.Icc 0 geometryBudget ∧ Prho ∈ Set.Icc 0 geometryBudget ∧
      Ptail ∈ Set.Icc 0 geometryBudget ∧
      (∀ Vtail : Fin m → ℝ≥0, (∀ j, (Vtail j : ℝ) ≤ Real.exp Palloc) →
        (probabilityProfileLipschitz : ℝ) ≤ Real.exp Palloc →
        let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)
        let α := allocatedModelUnitThreshold u pModel
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) Ctail
        Ctail ≤ Real.exp pModel ∧ Real.exp (-aDetect) ≤ α) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ {W Qw : ℝ}, 1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 geometryBudget ∧ Pk ≤ Pscale ∧
          (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog geometryBudget Qw) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
            (basis := basis) (S := S) (s := s) (nX := nX)
            Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
          (∀ lateTarget : ℝ, coarseTarget ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster sourceBudget geometryBudget Qw Pphysical lateTarget
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) sourceBudget Plate
            resources.nativeBudget ∈ Set.Icc 0 ((2 * sourceBudget + Cresource) ^ Cresource) ∧
            resources.required ∈ Set.Icc 0 ((sourceBudget + Plate + Cresource) ^ Cresource) ∧
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) sourceBudget sourceBudget).nativeBudget ∧
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
              [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              (Vtail : Fin m → ℝ≥0),
              PreparedModularGeneralDetectorInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (hb := hb) (o := o) Palloc Qstride sourceBudget Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro Cdetect Cresource Aalloc Cgeom Aearly Cphysical
  obtain ⟨C, hC, hsource⟩ := exists_preparedModularGeneralCanonicalPhysicalSource m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord P pSlice u Qstride hm hs hP hM hpSlice hu hQstride hnX
    Jalloc pnum Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D
    gainLog Pk Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K
    geometryBudget sourceBudget totalBudget
  obtain ⟨hPalloc, hnum, hGeometryBudget, hTotalBudget, hPhysicalMaster, hCoarseMaster,
      hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
      hcapacity, hkernelAllocation, hblockAllocation, hblockRows, hselection, houtputCount,
      hthreshold, pRadius, R, hpRadius, hpRadiusGeometry, hR,
      hModelGeometry, hDetectGeometry, haGeometry, hTargetGeometry, hDGeometry, hGainGeometry,
      hPkGeometry, hPrhoGeometry, hPtailGeometry, hTailCap, t, ht, htone, hsampler⟩ :=
    hsource L hCoord hm hs hP hM hpSlice hu hQstride hnX
  refine ⟨hPalloc, hnum, hGeometryBudget, hTotalBudget, hPhysicalMaster, hCoarseMaster,
    hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
    hcapacity, hkernelAllocation, hblockAllocation, hblockRows, hselection, houtputCount,
    hthreshold, pRadius, R, hpRadius, hpRadiusGeometry, hR,
    hModelGeometry, hDetectGeometry, haGeometry, hTargetGeometry, hDGeometry, hGainGeometry,
    hPkGeometry, hPrhoGeometry, hPtailGeometry, hTailCap, t, ht, htone, ?_⟩
  intro Wscale Qw hWscale hQw hWQw J _ U basis Pscale
  obtain ⟨S, hScaleGeometry, hPkScale, hSWitness, hgap, ⟨geometry⟩, hgainKernel⟩ :=
    hsampler hWscale hQw hWQw U basis
  refine ⟨S, hScaleGeometry, hPkScale, hSWitness, hgap, ⟨geometry⟩, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  have hAlloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hMaster : 0 ≤ sourceBudget := hPhysicalMaster.1.trans hPhysicalMaster.2
  have hGeometry0 : 0 ≤ geometryBudget := by
    dsimp only [geometryBudget]
    positivity
  have hLateTarget0 : 0 ≤ lateTarget := hCoarseMaster.1.trans hCoarseLower
  obtain ⟨hPlate0, hLate, hWitnessLate, hCoarseLate, hXiLate⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hMaster hGeometry0 hQw hPhysicalMaster.1 hLateTarget0
  obtain ⟨hNativeResource, hRequiredResource⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneral_uniform_resource_budget m)).2
      hMaster hLate ⟨s, Nat.lt_succ_of_le hs⟩
  refine ⟨hNativeResource, hRequiredResource, rfl, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ _ _ _ _ _ μrows _ _ _ _ Vtail
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff
  have hCphysical : 2 ≤ Cphysical :=
    (Classical.choose_spec (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)).1
  have hAllocMaster : Palloc ≤ sourceBudget := by
    have hbase : 1 ≤ Palloc + Cphysical := by
      have hcast : (2 : ℝ) ≤ Cphysical := Nat.cast_le.mpr hCphysical
      linarith only [hAlloc0, hcast]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cphysical)).trans
      (le_self_pow₀ hbase (by omega))
  have liftMaster {x : ℝ} (hx : x ∈ Set.Icc 0 geometryBudget) : x ∈ Set.Icc 0 sourceBudget :=
    ⟨hx.1, hx.2.trans hGeometryBudget⟩
  have hModelMaster := liftMaster hModelGeometry
  have hDetectMaster := liftMaster hDetectGeometry
  have hTargetMaster := liftMaster hTargetGeometry
  have hDMaster := liftMaster hDGeometry
  have hGainMaster := liftMaster hGainGeometry
  have hPkMaster := liftMaster hPkGeometry
  have hPrhoMaster := liftMaster hPrhoGeometry
  have hScaleMaster := liftMaster hScaleGeometry
  have hpRadiusMaster := hpRadiusGeometry.trans hGeometryBudget
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hPMaster : P ≤ sourceBudget := hPalloc.trans hAllocMaster
  have hExpMaster : Real.exp Palloc ≤ Real.exp sourceBudget := Real.exp_le_exp.mpr hAllocMaster
  obtain ⟨_, hSliceModel, _, hSliceLog, _, hCtail, _, hcountModel, _, _, _, _, _, hα, _, _⟩ :=
    preparedModularCanonicalDetector_early_cap L Jalloc A hCoord hAlloc0 hnum hpSlice.1 hu.1
      R Vtail hRpos (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
  have hMk := (hgainKernel _ hα).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
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
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).1
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
  have hDimPhysical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical := by
    have hsm : (s : ℝ) ≤ m := Nat.cast_le.mpr hs
    dsimp only [Pphysical]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith only [hQearly0, hPkMaster.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX, hsm]
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
  intro r τ' hτSpatial W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases hξn Z
  have hτInvMaster : τ'⁻¹ ≤ Real.exp sourceBudget := by
    rw [← one_div, hτinv]
    exact Real.exp_le_exp.mpr hPhysicalMaster.2
  have hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect (allocatedModelUnitThreshold u pModel
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B)))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))))
    Pphysical lateTarget
  have hξInvLate : ξn⁻¹ ≤ Real.exp Plate :=
    (preparedModularDetector_narrow_width B selection hPhysicalMaster.1 hLateTarget0
      (hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)) hDimPhysical hvarsPhysical hXPhysical).2.trans
      (Real.exp_le_exp.mpr hXiLate)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularGeneralDetector_late_positive_bounds B U basis S hb o μ ν hRpos hσpos
      (fun _ => htone) Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 hMaster hLate geometry.hdimensions
      hDMaster.2 (hnX.trans hPMaster)
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleMaster.2.trans hLate))) hSLate
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr (hQstride.2.trans hPMaster)))
      hτSpatial hτInvMaster hτhalf hτdim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have consumer := preparedModularGeneralDetectorLateCoarseInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hs Palloc D target Pk Prho Qstride sourceBudget Plate gainLog Pphysical lateTarget
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer hLate hMaster hDMaster.2 hPkMaster
    ⟨hQstride.1, hQstride.2.trans hPMaster⟩ hDetectMaster (hnX.trans hPMaster)
    (fun j => (hR j).2.1)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleMaster.2.trans hLate)))
    hSLate hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk hstride hstrideBound
    Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual
    (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate L Jalloc s hs ⟨j, Sum.inr i⟩)
    (fun j i => enlargedPreparedCommonSamplerBlock_uniform L Jalloc s hs ⟨j, Sum.inr i⟩)
    ⟨hu.1, hu.2.trans hPMaster⟩ hModelMaster hSliceModel hSliceLog hCtail hcountModel
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster.2 hCoarseLower hCoarseLate hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision.le hXiLate
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm
    budget' hξone'
  obtain ⟨_, hmodels⟩ := completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity
    hMk.2 hξone'
  exact hmodels

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_preparedModularDetectorBadProduct (m s : ℕ) (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Cresource := Classical.choose (exists_preparedModularGeneral_uniform_resource_budget m)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect)
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    let Cphysical := Classical.choose (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {P pSlice u Qstride : ℝ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → (M : ℝ) ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Palloc := (P + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := Palloc + (2 * Palloc + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
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
      let geometryBudget := (Palloc + Eextra + Cgeom) ^ Cgeom
      let sourceBudget := (Palloc + Cphysical) ^ Cphysical
      let totalBudget := (P + C) ^ C
      P ≤ Palloc ∧ pnum ≤ Palloc ∧ geometryBudget ≤ sourceBudget ∧ sourceBudget ≤ totalBudget ∧
      Pphysical ∈ Set.Icc 0 sourceBudget ∧ coarseTarget ∈ Set.Icc 0 sourceBudget ∧
      ξLog ∈ Set.Icc 0 sourceBudget ∧ 0 ≤ Eextra ∧
      coarseTarget + coefficientErrorSpatialLog Pphysical + 8 = target ∧
      0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧ 1 / τ = Real.exp Pphysical ∧
      (s + 1) * (s + 3) ≤ Fintype.card G ∧
      (∀ h : ℕ, h ≤ m → h * Jalloc ≤ Fintype.card G) ∧
      (∀ a : LayerSamplerAxis I n, Jalloc ≤ Fintype.card (B a)) ∧
      (∀ a : LayerSamplerAxis I n, (rowSets a.1).card ≤ Fintype.card (B a)) ∧
      (∀ i, (selection i).val = i.val) ∧
      (∀ inactive : LayerSamplerAxis I n → Prop,
        (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) I inactive j)) ≤
          nX + m * M) ∧
      ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
        modularRankSmallBallExponent m⌉₊ ≤ Jalloc ∧
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ geometryBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      pModel ∈ Set.Icc 0 geometryBudget ∧ pDetect ∈ Set.Icc 0 geometryBudget ∧
      aDetect ∈ Set.Icc 0 geometryBudget ∧ target ∈ Set.Icc 0 geometryBudget ∧
      D ∈ Set.Icc 0 geometryBudget ∧ gainLog ∈ Set.Icc 0 geometryBudget ∧
      Pk ∈ Set.Icc 0 geometryBudget ∧ Prho ∈ Set.Icc 0 geometryBudget ∧
      Ptail ∈ Set.Icc 0 geometryBudget ∧
      (∀ Vtail : Fin m → ℝ≥0, (∀ j, (Vtail j : ℝ) ≤ Real.exp Palloc) →
        (probabilityProfileLipschitz : ℝ) ≤ Real.exp Palloc →
        let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)
        let α := allocatedModelUnitThreshold u pModel
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) Ctail
        Ctail ≤ Real.exp pModel ∧ Real.exp (-aDetect) ≤ α) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ {B0 Ebad Vbad : ℝ} (Qbad : ℕ),
      1 ≤ B0 → sourceBudget ≤ B0 → Ebad ∈ Set.Icc 0 B0 → Vbad ∈ Set.Icc 0 B0 →
      1 ≤ Qbad → (Qbad : ℝ) ≤ Real.exp Vbad →
      let W := physicalBadProductGap (Jalloc * (nX + m * M)) Ebad Vbad Qbad
      let Qw := 2 * B0 + 2 * Vbad + 5 * Ebad + 24
      let J := fun j : Fin m => (L j).Coord
      letI : ∀ j, DecidableEq (J j) := fun _ => Classical.decEq _
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 geometryBudget ∧ Pk ≤ Pscale ∧
          (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog geometryBudget Qw) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
            (basis := basis) (S := S) (s := s) (nX := nX)
            Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
          PreparedSameScaleBadProductInterface L U basis S B0 Ebad Vbad Qbad ∧
          (∀ lateTarget : ℝ, coarseTarget ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster sourceBudget geometryBudget Qw Pphysical lateTarget
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) sourceBudget Plate
            resources.nativeBudget ∈ Set.Icc 0 ((2 * sourceBudget + Cresource) ^ Cresource) ∧
            resources.required ∈ Set.Icc 0 ((sourceBudget + Plate + Cresource) ^ Cresource) ∧
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m s) (s + 1) sourceBudget sourceBudget).nativeBudget ∧
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
              [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              (Vtail : Fin m → ℝ≥0),
              PreparedModularGeneralDetectorInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (hb := hb) (o := o) Palloc Qstride sourceBudget Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1)) ∧
            (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro Cdetect Cresource Aalloc Cgeom Aearly Cphysical
  obtain ⟨C, hC, hdetector⟩ := exists_preparedModularGeneralDetector m s Pdetect
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord P pSlice u Qstride hm hs hP hM hpSlice hu hQstride hnX
    Jalloc pnum Palloc G I n B selection A Pearly rowSets T siteRadius pModel pDetect aDetect D
    gainLog Pk Qearly Pphysical coarseTarget Eextra target τ Rspatial ξLog F Tmod δ E η Prho Ptail K
    geometryBudget sourceBudget totalBudget
  obtain ⟨hPalloc, hnum, hGeometryBudget, hTotalBudget, hPhysicalMaster, hCoarseMaster,
      hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
      hcapacity, hkernelAllocation, hblockAllocation, hblockRows, hselection, houtputCount,
      hthreshold, pRadius, R, hpRadius, hpRadiusGeometry, hR,
      hModelGeometry, hDetectGeometry, haGeometry, hTargetGeometry, hDGeometry, hGainGeometry,
      hPkGeometry, hPrhoGeometry, hPtailGeometry, hTailCap, t, ht, htone, hsampler⟩ :=
    hdetector L hCoord hm hs hP hM hpSlice hu hQstride hnX
  refine ⟨hPalloc, hnum, hGeometryBudget, hTotalBudget, hPhysicalMaster, hCoarseMaster,
    hXiMaster, hExtra, hprecision, hτ, hτhalf, hτdim, hτinv,
    hcapacity, hkernelAllocation, hblockAllocation, hblockRows, hselection, houtputCount,
    hthreshold, pRadius, R, hpRadius, hpRadiusGeometry, hR,
    hModelGeometry, hDetectGeometry, haGeometry, hTargetGeometry, hDGeometry, hGainGeometry,
    hPkGeometry, hPrhoGeometry, hPtailGeometry, hTailCap, t, ht, htone, ?_⟩
  intro B0 Ebad Vbad Qbad hB0 hSourceB0 hEbad hVbad hQbad hQbadExp W Qw J U basis Pscale
  have hAlloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hCphysical : 2 ≤ Cphysical :=
    (Classical.choose_spec (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)).1
  have hAllocMaster : Palloc ≤ sourceBudget := by
    have hbase : 1 ≤ Palloc + Cphysical := by
      have hcast : (2 : ℝ) ≤ Cphysical := Nat.cast_le.mpr hCphysical
      linarith only [hAlloc0, hcast]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cphysical)).trans
      (le_self_pow₀ hbase (by omega))
  have hnumB0 : pnum ≤ B0 := hnum.trans (hAllocMaster.trans hSourceB0)
  have hGeometryB0 : geometryBudget ≤ B0 := hGeometryBudget.trans hSourceB0
  have hPB0 : P ≤ B0 := hPalloc.trans (hAllocMaster.trans hSourceB0)
  have hQw : 0 ≤ Qw := by
    dsimp only [Qw]
    linarith only [hB0, hEbad.1, hVbad.1]
  obtain ⟨hW, hWexp⟩ := preparedBadProductWitnessGap_bounds m nX M hnumB0 hEbad.1 hVbad.1
    Qbad hQbad hQbadExp
  obtain ⟨S, hScaleGeometry, hPkScale, hSWitness, hgap, hgeometry, hdetectorLate, hgainKernel⟩ :=
    hsampler hW hQw hWexp U basis
  refine ⟨S, hScaleGeometry, hPkScale, hSWitness, hgap, hgeometry, ?_, hdetectorLate, hgainKernel⟩
  obtain ⟨geometry⟩ := hgeometry
  have hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp B0 := fun j =>
    (hR j).2.2.trans (Real.exp_le_exp.mpr (hpRadiusGeometry.trans hGeometryB0))
  have hσinv : ∀ j : Fin m, t⁻¹ ≤ Real.exp B0 := fun j =>
    (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleGeometry.2.trans hGeometryB0))
  have hSW : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog B0 Qw) :=
    hSWitness.trans (Real.exp_le_exp.mpr (allocatedWitnessScaleLog_mono
      (hDGeometry.1.trans hDGeometry.2) hGeometryB0 hQw le_rfl))
  apply preparedSameScaleBadProductInterface_of_bounds (m := m) (nX := nX) (M := M)
    (R := R) (σ := fun _ => t) (B := B0) (Elog := Ebad) (Vlog := Vbad) L U basis S Qbad
  · exact hB0
  · exact hM.trans hPB0
  · exact hnX.trans hPB0
  · exact hEbad
  · exact hVbad
  · exact hQbad
  · exact hQbadExp
  · exact hm
  · exact hCoord
  · exact hRinv
  · exact hσinv
  · exact hSW
  · exact hgap

end Erdos3.VectorPolynomial

end

end OAI
