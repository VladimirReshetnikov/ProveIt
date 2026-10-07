import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastGoodInterface

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedForecastLateScalarBounds
    {master Pseed Qw Pphysical lateTarget Pmin Pscale : ℝ}
    (hmaster : 0 ≤ master) (hseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hphysical : 0 ≤ Pphysical) (htarget : 0 ≤ lateTarget)
    (hmin : 0 ≤ Pmin) (hscale : 0 ≤ Pscale) :
    let base := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget
    let Plate := base + (1 + Pseed ^ 2) * Pmin + Pscale
    0 ≤ base ∧ base ≤ Plate ∧ master ≤ Plate ∧ Pscale ≤ Plate ∧
      allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤ Plate ∧
      (2 * (spatialPrimitiveEnvelope Pphysical lateTarget 0 +
        spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical lateTarget 0)) + 4) ≤ Plate := by
  intro base Plate
  obtain ⟨hbase, hmasterBase, hwitnessBase, _, hwidthBase⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hmaster hseed hQw hphysical htarget
  have hextra : 0 ≤ (1 + Pseed ^ 2) * Pmin :=
    mul_nonneg (by positivity) hmin
  have hbasePlate : base ≤ Plate := by
    change base ≤ base + (1 + Pseed ^ 2) * Pmin + Pscale
    linarith only [hextra, hscale]
  have hscalePlate : Pscale ≤ Plate := by
    change Pscale ≤ base + (1 + Pseed ^ 2) * Pmin + Pscale
    linarith only [hbase, hextra]
  have hwitnessPlate : allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤ Plate :=
    (add_le_add hwitnessBase (le_refl _)).trans (le_add_of_nonneg_right hscale)
  exact ⟨hbase, hbasePlate, hmasterBase.trans hbasePlate, hscalePlate,
    hwitnessPlate, hwidthBase.trans hbasePlate⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

structure PreparedForecastSourceScalarBounds
    (P Qearly Pphysical budget master Bstruct Pseed Qw lateTarget Pmin Pscale Plate : ℝ) : Prop where
  struct_input : Bstruct ≤ P
  P_nonneg : 0 ≤ P
  Qearly_nonneg : 0 ≤ Qearly
  physical_nonneg : 0 ≤ Pphysical
  master_nonneg : 0 ≤ master
  budget_master : budget ≤ master
  physical_master : Pphysical ≤ master
  struct_master : Bstruct ≤ master
  seed_nonneg : 0 ≤ Pseed
  Qw_nonneg : 0 ≤ Qw
  lateTarget_nonneg : 0 ≤ lateTarget
  base_nonneg : 0 ≤ preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget
  base_late : preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget ≤ Plate
  master_late : master ≤ Plate
  scale_late : Pscale ≤ Plate
  witness_late : allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin ≤ Plate
  xi_late : 2 * (spatialPrimitiveEnvelope Pphysical lateTarget 0 +
    spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical lateTarget 0)) + 4 ≤ Plate

theorem preparedForecastSourceScalarBounds (m nX Aearly : ℕ)
    {uModel pForecast Bstruct P Pearly budget pModel pDetect gainLog Pk Qstride
      D Pscale Prho target Tmod Pmin Vlog g₀ lateTarget : ℝ}
    (huModel : 0 ≤ uModel) (hpForecast : 0 ≤ pForecast) (hB : 0 ≤ Bstruct)
    (hmaster : Bstruct + (uModel + 2 * pForecast + 1) ≤ P)
    (hPEarly : P ≤ Pearly) (hEarlyBudget : Pearly ≤ budget)
    (hModel : pModel ∈ Set.Icc 0 budget) (hDetect : 0 ≤ pDetect)
    (hgain : 0 ≤ gainLog) (hPk : 0 ≤ Pk) (hQstride : 0 ≤ Qstride)
    (hD : 0 ≤ D) (hScale : 0 ≤ Pscale) (hPrho : 0 ≤ Prho)
    (htarget : 0 ≤ target) (hTmod : 0 ≤ Tmod)
    (hPmin : 0 ≤ Pmin) (hVlog : 0 ≤ Vlog) (hg : 0 ≤ g₀)
    (hCoarseLower : gainLog + 32 ≤ lateTarget) :
    let Qearly := (P + Aearly) ^ Aearly
    let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
    let master := budget + Pphysical + Pearly + gainLog + 32
    let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target (pDetect + 2) Tmod
    let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (g₀ + 8) + 24
    let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
      (1 + Pseed ^ 2) * Pmin + Pscale
    PreparedForecastSourceScalarBounds P Qearly Pphysical budget master Bstruct
      Pseed Qw lateTarget Pmin Pscale Plate := by
  intro Qearly Pphysical master lengthLog Pseed Qw Plate
  have hu : 0 ≤ uModel + 2 * pForecast + 1 := by positivity
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have hQearly : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  have hphysical : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hQearly hPk)
      hQstride) (Nat.cast_nonneg nX)) (Nat.cast_nonneg (m + 1))) (by norm_num)
  have hearly : 0 ≤ Pearly := hP.trans hPEarly
  have hbudget : 0 ≤ budget := hModel.1.trans hModel.2
  have hMaster : 0 ≤ master := by
    dsimp only [master]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg hbudget hphysical) hearly) hgain)
      (by norm_num)
  have hBudgetMaster : budget ≤ master := by
    dsimp only [master]
    linarith only [hphysical, hearly, hgain]
  have hPhysicalMaster : Pphysical ≤ master := by
    dsimp only [master]
    linarith only [hbudget, hearly, hgain]
  have hBMaster : Bstruct ≤ master :=
    hBP.trans (hPEarly.trans (hEarlyBudget.trans hBudgetMaster))
  have hF : 0 ≤ pDetect + 2 := by linarith only [hDetect]
  have hlength : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD hScale hPrho hPk htarget hF hTmod).2.2.1
  have hseed : 0 ≤ Pseed := allocatedScaleLog_nonneg
    (add_nonneg (add_nonneg (add_nonneg hD hScale) hlength) (by norm_num))
  have hQw : 0 ≤ Qw := by dsimp only [Qw]; positivity
  have hlateTarget : 0 ≤ lateTarget :=
    hgain.trans ((le_add_of_nonneg_right (by norm_num)).trans hCoarseLower)
  obtain ⟨hBase0, hBaseLate, hLate, hScaleLate, hWitnessLate, hXiLate⟩ :=
    preparedForecastLateScalarBounds hMaster hseed hQw hphysical hlateTarget hPmin hScale
  exact ⟨hBP, hP, hQearly, hphysical, hMaster, hBudgetMaster, hPhysicalMaster, hBMaster,
    hseed, hQw, hlateTarget, hBase0, hBaseLate, hLate, hScaleLate, hWitnessLate, hXiLate⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem preparedForecastSource_width
    {X J₀ : Type} {m M nX : ℕ} (L : RankPreparationFamily X J₀ m)
    (Jalloc A : ℕ) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m Jalloc)
    (Pdetect : Polynomial ℕ) (R : Fin m → ℝ) (Vtail : Fin m → ℝ≥0)
    {P pRadius pSlice uModel pForecast pModel Pk Pphysical coarseTarget Pwidth : ℝ}
    (hP : 0 ≤ P)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ P)
    (hpSlice : 0 ≤ pSlice) (hR : ∀ j, 0 < R j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hRadius : pRadius ≤ P + (2 * P + A) ^ A + 2)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hu : 0 ≤ uModel) (hp : 0 ≤ pForecast) (hModel : 0 ≤ pModel)
    (hForecast : allocatedEarlyModelLog (P + (2 * P + A) ^ A + 2) pSlice
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
        (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
        (EnlargedPreparedCommonSamplerBlock L Jalloc))) ≤ pForecast)
    {forecastCap : ℝ} (hForecastCap : forecastCap ≤ Real.exp pForecast)
    (hphysical : 0 ≤ Pphysical) (hcoarse : 0 ≤ coarseTarget)
    (hPk : Pk ≤ Pphysical) (hDim : (2 : ℝ) ≤ Pphysical)
    (hnumPhysical : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ Pphysical)
    (hnPhysical : (nX : ℝ) ≤ Pphysical)
    (hwidth : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4 ≤ Pwidth)
    (hkernel : ∀ α : ℝ, Real.exp (-(2 * (uModel + 2 * pForecast + 1) + 4 * pModel + 7)) ≤ α →
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m Jalloc)
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
          (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
          (EnlargedPreparedCommonSamplerBlock L Jalloc))) Pdetect
        (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel)
        (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel) α : ℝ) ≤ Real.exp Pk) :
    (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock L Jalloc)
        (layerSamplerDegree (PreparedSamplerContinuous L) (preparedSamplerTransverse L))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m Jalloc)
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
          (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
          (EnlargedPreparedCommonSamplerBlock L Jalloc))) Pdetect
        (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel)
        (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel)
        (forecastAugmentedUnitThreshold uModel pForecast
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
            (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
            (EnlargedPreparedCommonSamplerBlock L Jalloc))))
          (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous L j))
            (preparedSamplerTransverse L j) (R j) (Vtail j))) forecastCap / 2))
      Pphysical coarseTarget)⁻¹ ≤ Real.exp Pwidth := by
  have hc := preparedModularCanonicalDetector_early_cap L Jalloc A hCoord
    hP hnum hpSlice (le_refl (0 : ℝ)) R Vtail hR hRi hRadius hVtail hprofile
  have hcap := marginalCap_max_one_exp_bound hp
    (hc.2.2.2.2.2.1.trans (Real.exp_le_exp.mpr hForecast))
  have hα := (forecastAugmented_separate_source_precision hu hp hModel
    (Real.exp_nonneg _) (zero_le_one.trans hcap.1)
    (Real.exp_le_exp.mpr (hc.2.2.2.1.trans hForecast)) hcap.2 hForecastCap).2
  have hk := (hkernel _ hα).trans (Real.exp_le_exp.mpr hPk)
  obtain ⟨hvars, _, _⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  exact (preparedModularDetector_narrow_width (EnlargedPreparedCommonSamplerBlock L Jalloc)
    selection hphysical hcoarse hk hDim ((Nat.cast_le.mpr hvars).trans hnumPhysical)
    hnPhysical).2.trans (Real.exp_le_exp.mpr hwidth)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
local notation "kernel" => EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))
local notation "blocks" => EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
local notation "axes" => PreparedSamplerContinuous prep
local notation "transverse" => preparedSamplerTransverse prep
local notation "coords" => (fun j : Fin m => RankPreparationLayer.Coord (prep j))
variable (U : ∀ j, Submodule ℝ (coords j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (transverse j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := kernel) (I := axes) (n := transverse) (J := coords) blocks U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (0 + 1))))
variable (selection : Fin (0 + 1) ↪ kernel) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "qDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (axes j)) (transverse j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables kernel axes transverse blocks))
variable (τ u p forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := axes) U b S.value
local notation "degree" => layerSamplerDegree axes transverse
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => blocks (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => blocks (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides blocks U b S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos blocks U b S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (axes j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource blocks U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource blocks U b hR hσ S
local notation "reference" => allocatedLongJetReference blocks U b S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (0 + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity blocks U b hb o hR hσ S

structure PreparedCenteredShortForecastGoodBounds
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ) (D : ℝ) : Prop where
  hcert : PreparedShortCertifiedSameScaleBadProductInterface (nX := nX) (M := M) prep U b S B0 (gainLog + 8) Vlog Qgood
  hnX : 0 < nX
  hσ1 : ∀ j, σ j ≤ 1
  hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4
  hMaster : 0 ≤ Pmaster
  hLate : Pmaster ≤ Plate
  hd : AllocatedComparisonDimensions (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1)) (fun j : Fin m => (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1) : Type)) D
  hD : D ≤ Pmaster
  hnMaster : (nX : ℝ) ≤ Pmaster
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate
  hS : (S.value : ℝ) ≤ Real.exp Plate
  hchartB : Pchart ≤ B0
  hprojection : (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj ≤ Pwidth
  hphysical : jointPhysicalBaseLog Pwidth (gainLog + 8) Vlog ≤ B0
  hVlog : 0 ≤ Vlog
  hQexp : (Qgood : ℝ) ≤ Real.exp Vlog
  hP₀ : 0 ≤ P₀
  hnP₀ : (nX : ℝ) ≤ P₀
  hgP₀ : gainLog ≤ P₀
  hcutoffP : (P₀ + preparedCenteredShortForecastSpatialExponent m) ^
      preparedCenteredShortForecastSpatialExponent m ≤ Pgood
  hBP : B0 ≤ Pgood
  hwidthP : Pwidth ≤ Pgood
  hg : 0 ≤ gainLog
  hgP : gainLog + 8 ≤ Pgood
  hgain : Real.exp (-gainLog) ≤ gain
  hstrideWidth : Qstride ≤ Pwidth
  hτWidth : Pphysical ≤ Pwidth
  hξWidth : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Pwidth

theorem preparedCenteredShortForecastGoodExtraData
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
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
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
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : PreparedCenteredShortForecastGoodBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood D) :
    PreparedCenteredForecastModelExtraDataInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o)
      (Good := PreparedCenteredShortForecastGoodProperty (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ
        stride gainLog gain Qgood spatialEmbedding)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      (preparedCenteredShortForecastGoodRequired m B0 Pgood) := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff Eforecast hτSpatial hτInv hτHalf hτDim
    r W ξn hW hξone Pmarginal modelRequired required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases hξn Z hN hbases hbox hmass hnormalizer hmargin
    Path Zcenter hnormalizerCenter centeredLaw
  have hsizeGood (i) : Real.exp (preparedCenteredShortForecastGoodRequired m B0 Pgood) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hsize i)
  have hRankGood : Real.exp (preparedCenteredShortForecastGoodRequired m B0 Pgood) ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans hRank
  exact (exists_preparedCentered_short_forecastGoodData m).choose_spec.choose_spec.2.2.2 (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) prep U b S B0 Vlog gainLog gain Qgood H.hcert
    bW hb o Cforward Vtail hforward hVactual hR hσ H.hσ1 C hC hchart
    (H.hsmall C hC hCbound)
    (Pchart := Pchart) (Pmaster := Pmaster) (Plate := Plate) (D := D)
    (Pwidth := Pwidth) (P₀ := P₀) (P := Pgood)
    hprofile hForward hVtail H.hchartB H.hMaster H.hLate H.hd H.hD H.hnMaster H.hRi H.hσi H.hS
    H.hprojection H.hphysical H.hVlog H.hQexp H.hP₀ H.hnP₀ H.hgP₀ H.hcutoffP H.hBP H.hwidthP H.hg H.hgP H.hgain
    μ ν poly hpoly hmem stride hstride
    (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr H.hstrideWidth))
    hτSpatial (hτInv.trans (Real.exp_le_exp.mpr H.hτWidth)) hξn hξone H.hξWidth
    N hN hsizeGood hrank hRankGood cells hCells bases hbases hmass
    hnormalizerCenter H.hnX spatialEmbedding

theorem preparedCenteredShortForecastGoodModelInterface_of_model
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
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
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
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : PreparedCenteredShortForecastGoodBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood D)
    (hModel : PreparedCenteredForecastModelInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    PreparedCenteredShortForecastGoodModelInterface (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding := by
  apply preparedCenteredForecastModelExtension_of_model
    (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    (Good := PreparedCenteredShortForecastGoodProperty (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ
      stride gainLog gain Qgood spatialEmbedding)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    (preparedCenteredShortForecastGoodRequired m B0 Pgood) hModel
  exact preparedCenteredShortForecastGoodExtraData (m := m) (nX := nX) (M := M)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    B0 Vlog gainLog gain Pwidth P₀ Pgood Qgood spatialEmbedding
    H

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

structure PreparedShortForecastSourceRawBounds
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget : ℝ)
    (baseB0 Vlog gainLog gain Pwidth : ℝ) (Qgood : ℕ) (D : ℝ) : Prop where
  hcert : ∀ Bcert : ℝ, baseB0 ≤ Bcert →
    PreparedShortCertifiedSameScaleBadProductInterface (nX := nX) (M := M) prep U b S Bcert (gainLog + 8) Vlog Qgood
  hnX : 0 < nX
  hσ1 : ∀ j, σ j ≤ 1
  hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4
  hMaster : 0 ≤ Pmaster
  hLate : Pmaster ≤ Plate
  hd : AllocatedComparisonDimensions (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1)) (fun j : Fin m => (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1) : Type)) D
  hD : D ≤ Pmaster
  hnMaster : (nX : ℝ) ≤ Pmaster
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate
  hS : (S.value : ℝ) ≤ Real.exp Plate
  hprojection : (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj ≤ Pwidth
  hVlog : 0 ≤ Vlog
  hQexp : (Qgood : ℝ) ≤ Real.exp Vlog
  hg : 0 ≤ gainLog
  hgain : Real.exp (-gainLog) ≤ gain
  hstrideWidth : Qstride ≤ Pwidth
  hτWidth : Pphysical ≤ Pwidth
  hξWidth : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Pwidth
  hbase : 0 ≤ baseB0
  hchart : 0 ≤ Pchart
  hwidth : 0 ≤ Pwidth
  hnChart : (nX : ℝ) ≤ Pchart
  hgChart : gainLog ≤ Pchart

theorem preparedShortForecastSourceRawBounds_to_good
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget : ℝ)
    (baseB0 Vlog gainLog gain Pwidth : ℝ) (Qgood : ℕ) (D : ℝ)
    (H : PreparedShortForecastSourceRawBounds prep U b S selection Pdetect uSource pModel pSlice Vtail u p forecastCap
      Pchart Qstride Pmaster Plate Pphysical coarseTarget baseB0 Vlog gainLog gain Pwidth Qgood D) :
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    PreparedCenteredShortForecastGoodBounds prep U b S selection Pdetect uSource pModel pSlice
      Vtail u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget
      Bcert Vlog gainLog gain Pwidth Pchart Pgood Qgood D := by
  intro Bcert Pgood
  obtain ⟨_, hbaseCert, hchartCert, hphysicalCert, _, hcertGood, hwidthGood,
      hcutoffGood, hgainGood⟩ :=
    preparedForecastGoodBudgets (preparedCenteredShortForecastSpatialExponent m)
      H.hbase H.hchart H.hwidth H.hg H.hVlog
  exact {
    hcert := H.hcert Bcert hbaseCert
    hnX := H.hnX
    hσ1 := H.hσ1
    hsmall := H.hsmall
    hMaster := H.hMaster
    hLate := H.hLate
    hd := H.hd
    hD := H.hD
    hnMaster := H.hnMaster
    hRi := H.hRi
    hσi := H.hσi
    hS := H.hS
    hchartB := hchartCert
    hprojection := H.hprojection
    hphysical := hphysicalCert
    hVlog := H.hVlog
    hQexp := H.hQexp
    hP₀ := H.hchart
    hnP₀ := H.hnChart
    hgP₀ := H.hgChart
    hcutoffP := hcutoffGood
    hBP := hcertGood
    hwidthP := hwidthGood
    hg := H.hg
    hgP := hgainGood
    hgain := H.hgain
    hstrideWidth := H.hstrideWidth
    hτWidth := H.hτWidth
    hξWidth := H.hξWidth }

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

theorem preparedShortForecastRawSourceBounds
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (Vtail : Fin m → ℝ≥0) (A Aearly : ℕ)
    {Bstruct pRadius pSlice uModel pForecast pModel P Pearly budget gainLog Pk Qstride
      D Pscale Prho target Tmod Pmin Vlog g₀ lateTarget forecastCap gain : ℝ}
    (Qgood : ℕ)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct)
    (hnum : (enlargedPreparedCommonSamplerDimension m M
      (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ Bstruct)
    (hpRadius : pRadius ∈ Set.Icc 0 (Bstruct + (2 * Bstruct + A) ^ A + 2))
    (hpSlice : 0 ≤ pSlice)
    (hR : ∀ j, 0 < R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσ1 : ∀ j, σ j ≤ 1) (hσinv : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Bstruct) →
      ∀ j, C j * ((Fintype.card (PreparedSamplerContinuous prep j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hdimensions : AllocatedComparisonDimensions (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1) : Type)) D)
    (hnX : (nX : ℝ) ≤ Bstruct) (hnXpos : 0 < nX)
    (hg : 0 ≤ g₀) (hgStruct : g₀ ≤ Bstruct)
    (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (huModel : 0 ≤ uModel) (hpForecast : 0 ≤ pForecast)
    (hModelForecast : allocatedEarlyModelLog (Bstruct + (2 * Bstruct + A) ^ A + 2)
      pSlice (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) ≤ pForecast)
    (hmaster : Bstruct + (uModel + 2 * pForecast + 1) ≤ P)
    (hPEarly : P ≤ Pearly) (hEarlyBudget : Pearly ≤ budget)
    (hModel : pModel ∈ Set.Icc 0 budget)
    (hDetect : 0 ≤ allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel)
    (hgain : 0 ≤ gainLog) (hPk : 0 ≤ Pk) (hD : D ∈ Set.Icc 0 budget)
    (hScale : 0 ≤ Pscale) (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hTmod : 0 ≤ Tmod)
    (hpRadiusBudget : pRadius ≤ budget) (hPmin : 0 ≤ Pmin) (hVlog : 0 ≤ Vlog)
    (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hCoarseLower : gainLog + 32 ≤ lateTarget) (hAearly : 2 ≤ Aearly)
    (hForecastCapP : forecastCap ≤ Real.exp pForecast) (hGain : Real.exp (-g₀) ≤ gain)
    (hkernel : ∀ α : ℝ,
      Real.exp (-(2 * (uModel + 2 * pForecast + 1) + 4 * pModel + 7)) ≤ α →
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) Pdetect
          (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel)
          (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel) α : ℝ) ≤ Real.exp Pk) :
    let u := uModel + 2 * pForecast + 1
    let pDetect := allocatedModelTestLog u pModel
    let Qearly := (P + Aearly) ^ Aearly
    let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
    let master := budget + Pphysical + Pearly + gainLog + 32
    let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target (pDetect + 2) Tmod
    let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (g₀ + 8) + 24
    let B0 := 1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + (g₀ + 8) + Vlog
    let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
      (1 + Pseed ^ 2) * Pmin + Pscale
    let Pwidth := (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate).Pproj
    (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) →
    (∀ Bcert : ℝ, B0 ≤ Bcert →
      PreparedShortCertifiedSameScaleBadProductInterface (nX := nX) (M := M)
        prep U b S Bcert (g₀ + 8) Vlog Qgood) →
    PreparedShortForecastSourceRawBounds (m := m) (nX := nX) (M := M)
      prep U b S selection Pdetect u pModel pSlice Vtail uModel pForecast forecastCap
      Bstruct Qstride master Plate Pphysical lateTarget B0 Vlog g₀ gain Pwidth Qgood D ∧
      Bstruct ≤ master ∧ Qstride ≤ master ∧ Pphysical ≤ master ∧
      (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) Pdetect
          (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel)
          (allocatedModelTestLog (uModel + 2 * pForecast + 1) pModel)
        (forecastAugmentedUnitThreshold uModel pForecast
          (Real.exp (pSlice * (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))))
          (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j))
            ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap / 2)) Pphysical lateTarget)⁻¹ ≤ Real.exp Plate := by
  intro u pDetect Qearly Pphysical master lengthLog Pseed Qw B0 Plate Pwidth hSWitness hcert
  have hs := preparedForecastSourceScalarBounds m nX Aearly huModel hpForecast hB
    hmaster hPEarly hEarlyBudget hModel hDetect hgain hPk hQstride.1 hD.1
    hScale hPrho htarget hTmod hPmin hVlog hg hCoarseLower
  have hRiMaster := fun j => (hRi j).trans
    (Real.exp_le_exp.mpr (hpRadiusBudget.trans hs.budget_master))
  have hσLate := fun j => (hσinv j).trans (Real.exp_le_exp.mpr hs.scale_late)
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hs.witness_late)
  have hproj := preparedCenteredMarginalProjectionBounds
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S o hs.master_nonneg hs.master_late
    hdimensions (hD.2.trans hs.budget_master) (hnX.trans hs.struct_master)
    hRiMaster hσLate hSLate
  have hB00 : 0 ≤ B0 := by
    dsimp only [B0]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (by norm_num)
        (add_nonneg (add_nonneg hB hScale) hpRadius.1)) hs.seed_nonneg) hs.Qw_nonneg)
      hPmin) (add_nonneg hg (by norm_num))) hVlog
  have hPQ : P ≤ Qearly := preparedModularGeneralProductivity_le_budget hs.P_nonneg hAearly
  obtain ⟨hQPhysical, hDimPhysical, hnPhysical, hPkPhysical⟩ :=
    preparedModularGeneralProductivity_physical_bounds m 0 nX hs.Qearly_nonneg hPk hQstride.1
      (Nat.zero_le m)
  have hξ := preparedForecastSource_width (nX := nX) prep
    (modularInitialBlockCount m (nX + m * M)) A hCoord selection Pdetect R Vtail
    hB hnum hpSlice hR hRi hpRadius.2 hVtail hprofile huModel hpForecast hModel.1
    hModelForecast hForecastCapP hs.physical_nonneg hs.lateTarget_nonneg hPkPhysical hDimPhysical
    (hnum.trans (hs.struct_input.trans (hPQ.trans hQPhysical))) hnPhysical hs.xi_late hkernel
  refine ⟨?_, hs.struct_master, hQstride.2.trans hs.struct_master, hs.physical_master, hξ⟩
  exact ⟨hcert, hnXpos, hσ1, hsmall, hs.master_nonneg, hs.master_late, hdimensions,
    hD.2.trans hs.budget_master, hnX.trans hs.struct_master, hRiMaster, hσLate, hSLate,
    le_refl _, hVlog, hQexp, hg, hGain,
    hQstride.2.trans (hs.struct_master.trans hproj.master_projection),
    hs.physical_master.trans hproj.master_projection,
    hξ.trans (Real.exp_le_exp.mpr hproj.late_projection),
    hB00, hB, hproj.Pproj_nonneg, hnX, hgStruct⟩

end Erdos3.VectorPolynomial

end

end OAI
