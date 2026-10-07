import OAI.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorAmbientConsumer
import OAI.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorPositiveBounds
import OAI.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorSpatialBounds
import OAI.Combinatorics.Progressions.Sampling.PreparedModularCanonicalDetectorSamplingBounds

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

def PreparedModularCanonicalDetectorBudgetedInterface
    (Pchart P D target Pk Prho Qstride Pmaster pGain Pphysical : ℝ) (K : ℝ≥0) : Prop :=
    ∀ (_hMaster : 0 ≤ Pmaster) (_hDMaster : D ≤ Pmaster)
    (_hPkMaster : Pk ∈ Set.Icc 0 Pmaster) (_hQstrideMaster : Qstride ∈ Set.Icc 0 Pmaster)
    (_hDetectMaster : pDetect ∈ Set.Icc 0 Pmaster) (_hnXMaster : (nX : ℝ) ≤ Pmaster)
    (_hRone : ∀ j, R j ≤ 1)
    (_hRiMaster : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (_hσiMaster : ∀ j, (σ j)⁻¹ ≤ Real.exp Pmaster)
    (_hSMaster : (S.value : ℝ) ≤ Real.exp Pmaster)
    (_hKMaster : (K : ℝ) ≤ Real.exp Pmaster)
    (_hcutoffMaster : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pmaster)
    (_hMkP : ((allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (_hMkPk : ((allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForwardMaster : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pmaster)
    (_hVtailMaster : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pmaster)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (_hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (_huMaster : u ∈ Set.Icc 0 Pmaster) (_hModelMaster : pModel ∈ Set.Icc 0 Pmaster)
    (_hSliceModel : pSlice ≤ pModel)
    (_hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
    (_hCtail : Ctail ≤ Real.exp pModel)
    (_hcountModel : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp pModel)
    (_hPrhoMaster : Prho ∈ Set.Icc 0 Pmaster) (_htargetMaster : target ∈ Set.Icc 0 Pmaster)
    (_hGainMaster : pGain ∈ Set.Icc 0 Pmaster) (_hCoarseMaster : pGain + 32 ≤ Pmaster)
    (_hPhysicalMaster : Pphysical ∈ Set.Icc 0 Pmaster)
    (_hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) (_hDimPhysical : 2 ≤ Pphysical)
    (_hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (_hXPhysical : (nX : ℝ) ≤ Pphysical)
    (_hPkPhysical : Pk ≤ Pphysical) (_hQstridePhysical : Qstride ≤ Pphysical)
    (_hGainLog : slicedDetectionGainLog 0 (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect (2 * u + 4 * pModel + 7) ≤ pGain)
    (_hprecision : pGain + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target)
    (_hXiLog : 2 * (spatialPrimitiveEnvelope Pphysical (pGain + 32) 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical (pGain + 32) 0)) + 4 ≤ Pmaster),
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
    (0 + 1) * (0 + 3) ≤ Fintype.card G → (allocatedDetectedZeroKernelCutoff G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let budget := r.nativeBudget
    ∀ (hξone : ξn ≤ 1),
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

private theorem budgetedBoundary_exponential_small {x : ℝ} {d : ℕ}
    (hx : 2 ≤ x) (hd : (d : ℝ) ≤ x) :
    Real.exp (-x) ≤ 1 / 2 ∧ (d : ℝ) * Real.exp (-x) ≤ 1 / 2 := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have he : 2 * x ≤ Real.exp x := by
    nlinarith only [Real.quadratic_le_exp_of_nonneg hx0, sq_nonneg (x - 1)]
  constructor
  · rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos x)]
    linarith only [he, hx]
  · rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos x)]
    linarith only [he, hd]

include hb o bW μ ν μrows hR hσ in
theorem preparedModularCanonicalDetectorBudgetedInterface_of_geometry
    (Pchart D target Pk Prho Qstride Pmaster pGain Pphysical : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K) :
    PreparedModularCanonicalDetectorBudgetedInterface
      (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (hb := hb) (o := o)
      Pchart P D target Pk Prho Qstride Pmaster pGain Pphysical K := by
  intro hMaster hDMaster hPkMaster hQstrideMaster hDetectMaster hnXMaster hRone
    hRiMaster hσiMaster hSMaster hKMaster hcutoffMaster hMkP hMkPk hstride hstrideBound
    C hC hCbound hchart Cforward hforward hForwardMaster hVtailMaster hVactual hBa hBi
    huMaster hModelMaster hSliceModel hSliceLog hCtail hcountModel
    hPrhoMaster htargetMaster hGainMaster hCoarseMaster hPhysicalMaster hmPhysical hDimPhysical
    hvarsPhysical hXPhysical hPkPhysical hQstridePhysical hGainLog hprecision hXiLog
    r coarseTarget τ hτSpatial W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
  let constants := preparedModularCanonicalDetectorConstants m
  have hd := geometry.hdimensions
  have hmMaster : (m : ℝ) ≤ Pmaster := hd.degree.trans hDMaster
  have hJ := (allocatedProfile_dimensions U basis o B hd hb bW).1
  have hJMaster (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ Pmaster := (hJ j).trans hDMaster
  have hvarsMaster : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pmaster :=
    hvarsPhysical.trans hPhysicalMaster.2
  have hAsample : 2 ≤ constants.Asample :=
    (Classical.choose_spec (exists_allocatedCanonicalProjection_composed_budget m 1
      constants.Acover)).1
  have sampling := preparedModularDetector_sampling_bounds
    (J := J) (T := LayerSamplerVariables G I n B) stride constants rfl hMaster hAsample
    hmMaster hnXMaster (hvarsMaster.trans (by linarith only [hMaster]))
    (preparedModularDetector_ambient_count hJMaster) htargetMaster.2 hPhysicalMaster.2
    hQstrideMaster.2 hPkMaster.2 hstrideBound (hd.profile.trans hDMaster)
  have bounds := ((Classical.choose_spec
    (exists_preparedModularCanonicalDetector_resource_budget constants)).2 Pmaster hMaster).1
  obtain ⟨hDn, hgridn, hvn, hFn, hBn, hPnative, hprimitiveNative⟩ :=
    preparedModularCanonicalDetector_native_inputs constants hMaster
  obtain ⟨_, _, hQlog, _, _, hFmodel⟩ :=
    preparedModularDetector_period_prefactor B U basis o hb bW hMaster hd hDMaster
      hnXMaster hPkMaster hQstrideMaster hDetectMaster ⟨hMaster, le_rfl⟩
  have hgrid := preparedModularCanonicalDetector_grid_resource_width_bound constants
    hMaster hDetectMaster hQlog
  have hCoarse : coarseTarget ∈ Set.Icc 0 Pmaster :=
    ⟨by dsimp only [coarseTarget]; linarith only [hGainMaster.1], hCoarseMaster⟩
  have hAmbient := preparedModularCanonicalDetector_ambient_bound constants hMaster
    (hd.outputs.trans hDMaster) ⟨bounds.Pbox.1, le_rfl⟩ hPrhoMaster
    ⟨bounds.Vlog.1, le_rfl⟩ ⟨bounds.Nlog.1, le_rfl⟩ ⟨bounds.Q.1, le_rfl⟩ htargetMaster
    ⟨bounds.baseAmbient.1, le_rfl⟩
  have hMkPhysical := hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)
  have hGPhysical : (Fintype.card G : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsPhysical
  obtain ⟨_, hXi⟩ := preparedModularDetector_narrow_width B selection hPhysicalMaster.1
    hCoarse.1 hMkPhysical hDimPhysical hvarsPhysical hXPhysical
  have hXiProj : ξn⁻¹ ≤ Real.exp r.Pproj :=
    hXi.trans (Real.exp_le_exp.mpr (hXiLog.trans sampling.primitive_projection))
  have hRoot := preparedModularDetector_physical_root_of_variables B U basis S hMaster
    hvarsMaster hSMaster
  have hRootLog : 2 * Pmaster + 8 ≤ r.Pproj := by
    change 2 * Pmaster + 8 ≤ 4 * (Pmaster + 8)^2
    nlinarith only [hMaster, sq_nonneg Pmaster]
  have hWproj : W ≤ Real.exp r.Pproj := hRoot.trans (Real.exp_le_exp.mpr hRootLog)
  have hExpProj : Real.exp Pmaster ≤ Real.exp r.Pproj :=
    Real.exp_le_exp.mpr sampling.primitive_projection
  have hCtail0 : 0 ≤ Ctail := by
    apply mul_nonneg (by norm_num)
    exact Finset.prod_nonneg (fun j _ =>
      earlyConstantDensityCap_nonneg _ _ (hR j) (Vtail j).coe_nonneg)
  have hAlpha := (allocatedModelUnitThreshold_bounds huMaster.1 hModelMaster.1
    (Real.exp_nonneg _) hCtail0 (Real.exp_le_exp.mpr hSliceLog) hCtail).2.2
  have hGain := allocatedDetectedZeroGain_lower
    (Fintype.card (LayerSamplerVariables G I n B)) Pdetect hAlpha hGainLog
  obtain ⟨hReqSample, hReqMass, hReqProj, hReqSide, hReqFull⟩ :=
    preparedModularCanonicalDetector_required_bounds constants hMaster
  have hSize (x : ℝ) (hx : x ≤ r.required) (i : Fin nX) : Real.exp x ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hx).trans (hNlarge i)
  have hRank (x : ℝ) (hx : x ≤ r.required) : Real.exp x ≤ Rrank :=
    (Real.exp_le_exp.mpr hx).trans hRankLarge
  have hFull : (max r.Pproj r.E + constants.Amarginal)^constants.Amarginal ≤ r.required := by
    apply le_trans _ hReqFull
    apply pow_le_pow_left₀
      (add_nonneg (le_max_of_le_left bounds.Pproj.1) (Nat.cast_nonneg _))
    exact add_le_add
      (max_le (le_add_of_nonneg_right bounds.E.1) (le_add_of_nonneg_left bounds.full.1)) le_rfl
  have hNative := preparedModularCanonicalDetectorAmbientConsumer
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    Pchart D target Pk Prho Qstride K geometry hMaster hDMaster hPkMaster hQstrideMaster
    hDetectMaster hnXMaster hRone hRiMaster hσiMaster hSMaster hKMaster hcutoffMaster
    hMkP hMkPk hstride hstrideBound C hC hCbound hchart Cforward hforward
    hForwardMaster hVtailMaster hVactual hBa hBi
    (Pproj := r.Pproj) (coarseTarget := coarseTarget) (Ecoarse := coarseTarget) (pGain := pGain)
    (τ := τ) (Pphysical := Pphysical) (Pnative := r.Pnative) (Pside := r.Pside)
    cells poly hp hmem
    (lossTarget := coarseTarget) (Psample := r.Psample) (Rrank := Rrank)
    (Sstride := Real.exp Qstride) (εsample := Real.exp (-target)) (ηsample := Real.exp (-target))
    hstride (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hτSpatial sampling.sample_nonneg
    sampling.X_sample sampling.frame_sample sampling.stride_scale_nonneg sampling.stride_scale_sample
    sampling.precision_pos sampling.tau_sample sampling.epsilon_sample hstrideBound
    (hSize _ hReqSample) hrank (hRank _ hReqSample) sampling.precision_pos
    sampling.ambient_dimension_sample (hAmbient.2.2.trans sampling.ambient_sample)
    sampling.jet_sample sampling.eta_sample hPhysicalMaster.1 hMkPhysical hmPhysical hCoarse.1
    hDimPhysical hGPhysical (by simpa only [Fintype.card_fin] using hXPhysical)
    hprecision le_rfl le_rfl
  have hNative := hNative
    (hMaster.trans hPnative) hDn
    (by change 0 ≤ _ ∧ _ ≤ _
        have hCgrid : constants.Cgrid = Classical.choose
            (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (0 + 1) canonicalTransitionLip) := rfl
        rw [← hCgrid]
        simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, one_add_one_eq_two]
          using And.intro hgrid.1 (hgrid.2.trans hgridn.2)) hvn
    (by change 0 ≤ _ ∧ _ ≤ _
        simpa only [add_assoc] using And.intro hFmodel.1 (hFmodel.2.trans hFn.2))
    (hprimitiveNative _ hPrhoMaster) (hprimitiveNative _ hPkMaster)
    (hprimitiveNative _ htargetMaster) hBn (hprimitiveNative _ hPhysicalMaster)
    (hprimitiveNative _ hCoarse) (hprimitiveNative _ hGainMaster)
    (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr hQstridePhysical))
    (by dsimp only [τ]; rw [one_div, Real.exp_neg, inv_inv])
    hGain (by linarith only [hGainMaster.2, sampling.gain_projection]) le_rfl le_rfl le_rfl
    Cforward sampling.cover_base sampling.cover_sample sampling.mass_sample hforward hVactual
    sampling.X_mass sampling.frame_mass sampling.stride_mass sampling.tau_mass
    (hSize _ hReqMass) (hRank _ hReqMass) sampling.ambient_dimension_mass sampling.jet_mass
    (hvarsPhysical.trans (by linarith only [Real.add_one_le_exp Pphysical]))
    sampling.projection_one (hmMaster.trans sampling.primitive_projection)
    ((hd.kernel_variables.trans hDMaster).trans sampling.primitive_projection)
    (hSMaster.trans hExpProj) sampling.period_projection sampling.variables_projection hWproj
    (fun j => (hRiMaster j).trans hExpProj) (fun j => (hσiMaster j).trans hExpProj)
    (fun j => ((hd.coefficients j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (((preparedModularDetector_layer_axes B rowSets hd).1 j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (((preparedModularDetector_layer_axes B rowSets hd).2 j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (hJMaster j).trans sampling.primitive_projection) sampling.profile_projection
    (fun j => (hForwardMaster j).trans hExpProj) (fun j => (hVtailMaster j).trans hExpProj)
    sampling.X_projection sampling.frame_projection sampling.stride_projection sampling.tau_projection
    hXiProj (hSize _ hReqProj) (hRank _ hReqProj)
  have hNative := hNative sampling.projection_side sampling.mass_side
    sampling.physical_side (hCoarseMaster.trans sampling.primitive_side) (hSize _ hReqSide)
  intro hCells bases hbases hξn hmass htotal Path pathLaw sides Sites e
    Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hslices hdense hdimensionDetect hcomplexity hcap hGdetect hkernel budget hξone
  have hBoundary := budgetedBoundary_exponential_small hDimPhysical hXPhysical
  exact hNative hCells hbases hmass htotal Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hslices hdense hdimensionDetect hcomplexity hcap hGdetect hkernel
    huMaster.1 hModelMaster.1 bounds.nativeBudget.1 hSliceModel hSliceLog hCtail hcountModel
    (fun j => (geometry.hσsmall j).trans geometry.htone) (geometry.hbudgets C hC hCbound).1
    hBoundary.1 (by simpa only [Fintype.card_fin] using hBoundary.2) hξone
    (Efull := r.E) (hSize _ hFull) (hRank _ hFull)
    (preparedModularCanonicalDetector_final_error_bound constants huMaster.2 hModelMaster.2)

end Erdos3.VectorPolynomial

end

end OAI
