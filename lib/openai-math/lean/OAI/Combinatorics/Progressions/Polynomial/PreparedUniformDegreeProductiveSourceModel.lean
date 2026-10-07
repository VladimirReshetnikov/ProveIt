import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
import OAI.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastSourceModelAttachment

namespace OAI


namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

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
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "qDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ u p forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include ν in

theorem preparedUniformDegreeModelChain
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) («α» := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    {D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) selectedRows D)
    (hD : D ≤ Pmaster) (hnX : (nX : ℝ) ≤ Pmaster)
    (hChartMaster : Pchart ≤ Pmaster) (hStrideMaster : Qstride ≤ Pmaster)
    (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) (hσone : ∀ j, σ j ≤ 1)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  have hProjection := sharedWidthPreparedCenteredModelMarginalProjectionData_of_direct
    B U basis hR hσ S selection stride N Pdetect uSource pModel pSlice Vtail α τ hb o ν μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect hMaster hLate
    hd hD hnX hChartMaster hStrideMaster hPhysicalMaster hRP hσLate hLLate hσone
  have hRadius := sharedWidthPreparedCenteredModelMarginalRadiusInterface_of_projection
    B U basis hR hσ S selection stride N Pdetect uSource pModel pSlice Vtail α τ hb o μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hProjection hsmall
  exact sharedWidthPreparedCenteredForecastModelInterface_of_radius
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hMaster hLate
    hu hp hSliceLog hCtail hForecastCap hForecastCapP hRadius

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

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
variable (u p : ℝ)
local notation "uSource" => u + 2 * p + 1
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "qDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

include ν bW μrows in

theorem preparedUniformDegreeGeometryModel
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius uSource pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * uSource + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (0 + 1) * (0 + 3) ≤ Fintype.card G)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget ∧
    (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect pDetect (α / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  have hKp : Kslice ≤ Real.exp p := Real.exp_le_exp.mpr hSliceLog
  have hCap := marginalCap_max_one_exp_bound hp hCtail
  have hC : 0 ≤ max 1 Ctail := zero_le_one.trans hCap.1
  have hαlower := (forecastAugmented_separate_source_precision hu hp scalar.model_master.1
    (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2
  have hαone : α / 2 ≤ 1 := by
    have h := (forecastAugmentedUnitThreshold_bounds hu hp
      (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2.1
    linarith only [h]
  have hDirect := preparedUniformDegreeDirectSource_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) («α» := α / 2) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    (Nat.zero_le m) Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain
    Pphysical coarseTarget pRadius scalar geometryAt hRone hRinv hσone hSLate
    hBa hBi hcapacity hαlower hαone
  obtain ⟨⟨geometry⟩, hgainKernel⟩ := geometryAt
  constructor
  · exact preparedUniformDegreeModelChain
      (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (ν := ν) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
      scalar.master_nonneg scalar.late geometry.hdimensions scalar.dimension_master
      scalar.ambient_master scalar.chart_master scalar.stride_master.2 scalar.physical_master.2
      (fun j => (hRinv j).trans (Real.exp_le_exp.mpr scalar.radius_master))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late))
      hSLate hσone (fun C hC hBound => (geometry.hbudgets C hC hBound).1)
      hu hp hSliceLog hCtail hForecastCap hForecastCapP
  · have hMk := (hgainKernel (α / 2) hαlower).2.1
    have hCoarse : 0 ≤ coarseTarget := by
      linarith only [scalar.gain_master.1, scalar.coarse_lower]
    have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
      hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
      scalar.detector_physical scalar.variables_physical scalar.ambient_physical
    exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m nX : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable (Jalloc : ℕ)
local notation "G" => EnlargedPreparedCommonKernel m Jalloc
local notation "I" => PreparedSamplerContinuous prep
local notation "n" => preparedSamplerTransverse prep
local notation "B" => EnlargedPreparedCommonSamplerBlock prep Jalloc
local notation "selection" => enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b R σ)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
local notation "uSource" => u + 2 * p + 1
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ
  (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
  (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep)
  (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
  (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep)
  (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
  (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep)
  (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
  (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous prep)
  (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep Jalloc)) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

include prep Jalloc hR hσ S stride N Pdetect pModel pSlice Vtail τ u p forecastCap hb o μ in
def PreparedUniformDegreeProductiveSourceModelConclusion
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ) : Prop :=
    SharedWidthPreparedCenteredForecastModelInterface
      (m := m) (nX := nX) («G» := G) («I» := I) («n» := n) (J := J)
      («B» := B) (U := U) (basis := b) (R := R) (σ := σ)
      (S := S) (hR := hR) (hσ := hσ)
      («selection» := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget ∧
    (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection (allocatedDetectedKernelCutoff 0 G
        (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect (α / 2))
      Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate

include prep Jalloc hR hσ hb o μ bW ν μrows in

theorem preparedUniformDegreeProductiveSourceModel
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius uSource pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt (m := m) («G» := G)
      («I» := I) («n» := n) (J := J) B U b S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * uSource + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    PreparedUniformDegreeProductiveSourceModelConclusion
      (prep := prep) (Jalloc := Jalloc) (U := U) (b := b) (R := R) (σ := σ)
      (hR := hR) (hσ := hσ)
      (S := S) (stride := stride) (N := N) (Pdetect := Pdetect)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  exact preparedUniformDegreeGeometryModel
    (m := m) (nX := nX) («G» := G) («I» := I) («n» := n) (J := J)
      («B» := B) (U := U) (basis := b) (R := R) (σ := σ)
      (S := S) (hR := hR) (hσ := hσ)
    («selection» := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
    (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν)
    (μ := μ) (μrows := μrows)
    Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate
    (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep Jalloc 0
      (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep Jalloc 0
      (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (enlargedPreparedCommonKernel_analytic_capacity m Jalloc 0 (Nat.zero_le m))
    hu hp hSliceLog hCtail hForecastCap hForecastCapP

end Erdos3.VectorPolynomial

end OAI
