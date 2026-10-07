import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSourceModel
import OAI.Combinatorics.Progressions.Sampling.PrecenterForecastNativePartners

namespace OAI

section

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
variable (sourceU : ℝ)
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog sourceU pModel
local notation "qDetect" => allocatedModelTestLog sourceU pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ : ℝ)

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

def PreparedScheduledModelAvailability
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ) : Prop :=
  ∀ (u p forecastCap : ℝ), sourceU = u + 2 * p + 1 →
    0 ≤ u → 0 ≤ p →
    pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p →
    Ctail ≤ Real.exp p → 0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget ∧
    (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect pDetect
        (forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap / 2))
      Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate

include ν bW μrows in

theorem preparedFiniteScheduleGeometryModel
    (degree Cdetect : ℕ) (hdegree : degree = 0)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant 0 Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m degree nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S degree Cdetect nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
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
    (hcapacity : (0 + 1) * (0 + 3) ≤ Fintype.card G) :
    PreparedScheduledModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro u p forecastCap hsource hu hp hslice htail hcap hcapP
  rw [hdegree, hCdetect, hsource] at scalar geometryAt
  rw [hsource]
  exact preparedUniformDegreeGeometryModel
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate hBa hBi hcapacity
    hu hp hslice htail hcap hcapP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))

def PreparedFiniteScheduleModelsAtLaw
    {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hbox : (integerBox N).Nonempty)
    (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Path → integerBox (Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U basis S)) → integerBox N)
    (uModel pInput cap sliceLog testLog budget E : ℝ) : Prop :=
    let pathLaw := centeredFiniteMarginal μ law hweight
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
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)) sliceLog ((slices z j).image e)) →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) testLog →
    (∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    let tests := fun z j t => star ((Vdetect z j).eval
      (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))
    ∀ {Forecast : Type} [Nonempty Forecast]
      (forecast : Forecast → integerBox N → ℂ)
      {PforecastNative massLog : ℝ},
      0 ≤ PforecastNative → 0 ≤ massLog →
      uModel + 2 * pInput + max (max budget (3 * PforecastNative + 3))
        (2 * uModel + 4 * pInput + massLog + 20) + 32 ≤ E →
    ∀ (Term : Forecast → Type) [∀ f, Fintype (Term f)]
      (coefficient : ∀ f, Term f → ℂ)
      (centerConstant : Forecast → ∀ j, J j → ℝ)
      (twists : ∀ f, Term f → NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp (3 * PforecastNative + 3)) (Real.exp (3 * PforecastNative + 3))
        ⟨Real.exp (3 * PforecastNative + 3), Real.exp_nonneg _⟩),
      (∀ f, (∑ i, ‖coefficient f i‖) ≤ Real.exp massLog) →
      (∀ f v, ‖forecast f v - ∑ i, coefficient f i *
        (twists f i).eval N (fun j => subtractConstant (centerConstant f j) (poly j)) v.val‖ ≤
          Real.exp (-(2 * uModel + 4 * pInput + 12))) →
      (∀ f v, ‖forecast f v‖ ≤ cap) →
    ∀ {Branch : Type} [Fintype Branch]
      (input : Branch → integerBox N → ℂ), (∀ branch v, ‖input branch v‖ ≤ Real.exp pInput) →
    let commonBudget := max budget (3 * PforecastNative + 3)
    let Qmodel := max commonBudget (2 * uModel + 4 * pInput + massLog + 20)
    let native := twistedNativeSampleFunctions (1 : Fin nX → ℕ) 0 commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm := sampledSliceSeminorm pathLaw physical slices tests
    let selectedLocal := fun (err : integerBox N → ℂ)
      (errLocal : CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) =>
      ∀ center z, ∃ j, errLocal (center, z) =
        𝔼 t ∈ slices z j, err (physical z t) * tests z j t
    ∃ models : Branch → CenteredForecastModel (integerBox N),
      ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        native (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) forecast
        localSeminorm selectedLocal (input branch) (Real.exp (Qmodel + 2))
        (Real.exp (-uModel)) (Real.exp (2 * Qmodel + 2 * uModel + 4 * pInput + 34))
        (models branch)

variable {Stage : Type} (kModel : Stage)
variable (uSource modelLog sliceLog uModel pInput forecastCap : Stage → ℝ)
variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

def PreparedFiniteScheduleModelExtensionInterface
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired : ℝ) : Prop :=
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
    ∀ {E : ℝ},
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn)
      (hξle : ∀ k, ξn ≤ normalizedTupleNarrowWidth (Fin nX)
        (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
        (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect (allocatedModelTestLog (uSource k) (modelLog k))
          (allocatedModelTestLog (uSource k) (modelLog k))
          (forecastAugmentedUnitThreshold (uModel k) (pInput k)
            (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
            (max 1 Ctail) (forecastCap k) / 2))
        Pphysical coarseTarget),
    ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    let hξone : ξn ≤ 1 := (hξle kModel).trans (min_le_left _ _)
    let Pmarginal := r.Pproj
    let modelRequired := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
    let required := max modelRequired extraRequired
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    let Zcenter := fun center => selectedJointDensityMass bases stride cells V
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
    ∃ hnormalizerCenter : ∀ center,
      |Zcenter center - 1| ≤ Real.exp (-E) ∧
      Zcenter center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Zcenter center ∧ (Zcenter center)⁻¹ ≤ 2,
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hnormalizerCenter center).2.2.1
    ∃ hweight : ∀ z, Measurable (fun center => (centeredLaw center).weight z),
    Good poly hmem V bases centeredLaw ∧
    let pathLaw := centeredFiniteMarginal μ centeredLaw hweight
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    letI : Nonempty Sites := by
      have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
        cases k with
        | inl g => exact S.positive
        | inr j => exact allocatedPrincipalSides_pos B U basis S j
      let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
      exact (integerBox_nonempty sides).to_subtype
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial hξone N hN
      _hmargin e hrootSum
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (pathLaw.siteLaw physical) Ctail ≤ 6 * positiveProjectionAccuracy E ∧
    ∀ k, PreparedFiniteScheduleModelsAtLaw B U basis S N Pdetect μ poly hbox
      centeredLaw hweight physical (uModel k) (pInput k) (forecastCap k) (sliceLog k)
      (allocatedModelTestLog (uSource k) (modelLog k)) r.nativeBudget E

theorem preparedFiniteScheduleModelAttachment
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired : ℝ)
    (pGain : Stage → ℝ)
    (hModels : ∀ k, SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource k) (pModel := modelLog k)
      (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (u := uModel k) (p := pInput k) (forecastCap := forecastCap k)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate (pGain k) Pphysical coarseTarget)
    (hGoodModel : SharedWidthPreparedCenteredForecastModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource kModel) (pModel := modelLog kModel)
      (pSlice := sliceLog kModel) (Vtail := Vtail) (τ := τ)
      (u := uModel kModel) (p := pInput kModel) (forecastCap := forecastCap kModel)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride Pmaster Plate (pGain kModel) Pphysical coarseTarget extraRequired) :
    PreparedFiniteScheduleModelExtensionInterface
      B U basis hR hσ S selection stride N Pdetect Vtail τ hb o μ
      kModel uSource modelLog sliceLog uModel pInput forecastCap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal modelRequired required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hnormalizerCenter,
      hweight, hgood, hexcess, _hbaseModel⟩ :=
    hGoodModel hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff (E := E) hτSpatial hτInv hτHalf hτDim
      hξn (hξle kModel) hξLate cells poly hpoly hmem hsize hrank hRank hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path Zcenter
  refine ⟨hnormalizerCenter, ?_⟩
  intro centeredLaw
  refine ⟨hweight, hgood, ?_⟩
  intro pathLaw sides Sites e hrootSum physical
  let : Nonempty Sites := by
    have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
      cases k with
      | inl g => exact S.positive
      | inr j => exact allocatedPrincipalSides_pos B U basis S j
    let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
    exact (integerBox_nonempty sides).to_subtype
  refine ⟨hexcess, ?_⟩
  intro k
  have hsizeStage (i) : Real.exp modelRequired ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans (hsize i)
  have hRankStage : Real.exp modelRequired ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans hRank
  obtain ⟨_hNk, _hbasesk, _hboxk, _hmassk, _hnormk, _hmargink,
      _hnormCenterk, _hweightk, _hexcessk, hstage⟩ :=
    hModels k hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff (E := E) hτSpatial hτInv hτHalf hτDim
      hξn (hξle k) hξLate cells poly hpoly hmem hsizeStage hrank hRankStage hCells
  unfold PreparedFiniteScheduleModelsAtLaw
  intro pathLaw' sides' Sites' e' Tests instTests Ldetect instLie instAlg dims
    instTopo instAdd instSmul instT2 Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hSlices hDense hnum hcomplex hcap tests Forecast instForecast forecast
    PforecastNative massLog hForecastNative hMassLog hModelPrecision
    Term instTerm coefficient centerConstant twists hCoeffMass hApprox hForecast
    Branch instBranch input hinput commonBudget Qmodel native localSeminorm selectedLocal
  have hsingle := hstage Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hSlices hDense hnum hcomplex hcap forecast hForecastNative hMassLog
    hModelPrecision Term coefficient centerConstant twists hCoeffMass hApprox hForecast
  have hsingleModel : ∀ f : integerBox N → ℂ, (∀ v, ‖f v‖ ≤ Real.exp (pInput k)) →
      ∃ model : CenteredForecastModel (integerBox N),
        CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ centeredLaw)
          native (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) forecast
          localSeminorm selectedLocal f (Real.exp (Qmodel + 2)) (Real.exp (-uModel k))
          (Real.exp (2 * Qmodel + 2 * uModel k + 4 * pInput k + 34)) model := by
    intro f hf
    obtain ⟨nterms, hpos, models, coeff, err, hspec⟩ := hsingle f hf
    exact ⟨⟨nterms, hpos, models, coeff, err⟩, hspec⟩
  exact exists_centeredFiniteForecastModels
    (centeredFiniteProbabilityMeasure μ centeredLaw) native
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) forecast
    localSeminorm selectedLocal input (Real.exp (pInput k)) (Real.exp (Qmodel + 2))
    (Real.exp (-uModel k)) (Real.exp (2 * Qmodel + 2 * uModel k + 4 * pInput k + 34))
    hinput hsingleModel

theorem preparedFiniteScheduleModelAttachment_of_availability
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired : ℝ)
    (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := uSource k) (pModel := modelLog k)
      (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate (pGain k) Pphysical coarseTarget)
    (hsource : ∀ k, uSource k = uModel k + 2 * pInput k + 1)
    (hu : ∀ k, 0 ≤ uModel k) (hp : ∀ k, 0 ≤ pInput k)
    (hslice : ∀ k, sliceLog k * Fintype.card (LayerSamplerVariables G I n B) ≤ pInput k)
    (htail : ∀ k, Ctail ≤ Real.exp (pInput k))
    (hcap : ∀ k, 0 ≤ forecastCap k) (hcapP : ∀ k, forecastCap k ≤ Real.exp (pInput k))
    (hGoodModel : SharedWidthPreparedCenteredForecastModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource kModel) (pModel := modelLog kModel)
      (pSlice := sliceLog kModel) (Vtail := Vtail) (τ := τ)
      (u := uModel kModel) (p := pInput kModel) (forecastCap := forecastCap kModel)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride Pmaster Plate (pGain kModel) Pphysical coarseTarget extraRequired) :
    PreparedFiniteScheduleModelExtensionInterface
      B U basis hR hσ S selection stride N Pdetect Vtail τ hb o μ
      kModel uSource modelLog sliceLog uModel pInput forecastCap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired ∧
    0 < Real.exp (-Plate) ∧ (Real.exp (-Plate))⁻¹ = Real.exp Plate ∧
    ∀ k, Real.exp (-Plate) ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (uSource k) (modelLog k))
        (allocatedModelTestLog (uSource k) (modelLog k))
        (forecastAugmentedUnitThreshold (uModel k) (pInput k)
          (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 Ctail) (forecastCap k) / 2)) Pphysical coarseTarget := by
  have hstage (k) := hAvailable k (uModel k) (pInput k) (forecastCap k)
    (hsource k) (hu k) (hp k) (hslice k) (htail k) (hcap k) (hcapP k)
  refine ⟨?_, ?_⟩
  · exact preparedFiniteScheduleModelAttachment B U basis hR hσ S selection stride N Pdetect
      Vtail τ hb o μ kModel uSource modelLog sliceLog uModel pInput forecastCap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired pGain
      (fun k => (hstage k).1) hGoodModel
  · exact sharedWidthNormalizedTuplePreparedChoice (fun _ : Stage => 0 + 1)
      (fun k => allocatedDetectedKernelCutoff 0 G
        (Fintype.card (LayerSamplerVariables G I n B)) Pdetect
        (allocatedModelTestLog (uSource k) (modelLog k))
        (allocatedModelTestLog (uSource k) (modelLog k))
        (forecastAugmentedUnitThreshold (uModel k) (pInput k)
          (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 Ctail) (forecastCap k) / 2))
      (fun _ => selection) (fun _ => Pphysical) (fun _ => coarseTarget) Plate
      (fun k => (hstage k).2)

end Erdos3.VectorPolynomial

end

end OAI
