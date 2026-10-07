import OAI.Combinatorics.Progressions.Estimates.DetectedCanonicalEarlyRadiusLateFloorSource
import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralDirectDetectionLateFloor
import OAI.Combinatorics.Progressions.Geometry.PreparedModularGeneralDetectorFreeSpatialBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

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
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (α τ : ℝ)
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

def PreparedModularGeneralDirectDetectionFreeTrimInterface
    (Pchart P D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ) (K : ℝ≥0) : Prop :=
    ∀ (_hLate : Pmaster ≤ Plate) (_hMaster : 0 ≤ Pmaster) (_hDMaster : D ≤ Pmaster)
    (_hPkMaster : Pk ∈ Set.Icc 0 Pmaster) (_hQstrideMaster : Qstride ∈ Set.Icc 0 Pmaster)
    (_hDetectMaster : pDetect ∈ Set.Icc 0 Pmaster) (_hnXMaster : (nX : ℝ) ≤ Pmaster)
    (_hRone : ∀ j, R j ≤ 1)
    (_hRiMaster : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (_hσiLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (_hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (_hKMaster : (K : ℝ) ≤ Real.exp Pmaster)
    (_hcutoffMaster : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pmaster)
    (_hMkP : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp P)
    (_hMkPk : ((allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) : ℝ) ≤ Real.exp Pk)
    (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForwardMaster : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pmaster)
    (_hVtailMaster : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pmaster)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (_hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (_huMaster : u ∈ Set.Icc 0 Pmaster) (_hModelMaster : pModel ∈ Set.Icc 0 Pmaster)
    (_hSliceModel : pSlice ≤ pModel)
    (_hcountModel : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp pModel)
    (_hαlower : Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α) (_hαone : α ≤ 1)
    (_hPrhoMaster : Prho ∈ Set.Icc 0 Pmaster) (_htargetMaster : target ∈ Set.Icc 0 Pmaster)
    (_hGainMaster : pGain ∈ Set.Icc 0 Pmaster) (_hCoarseMaster : pGain + 32 ≤ Pmaster)
    (_hCoarseLower : pGain + 32 ≤ coarseTarget) (_hCoarseLate : coarseTarget ≤ Plate)
    (_hPhysicalMaster : Pphysical ∈ Set.Icc 0 Pmaster)
    (_hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) (_hDimPhysical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical)
    (_hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (_hXPhysical : (nX : ℝ) ≤ Pphysical)
    (_hPkPhysical : Pk ≤ Pphysical) (_hQstridePhysical : Qstride ≤ Pphysical)
    (_hGainLog : slicedDetectionGainLog s (sampledSupportedSlicedDetectionConstant s Pdetect)
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect (2 * u + 4 * pModel + 7) ≤ pGain)
    (_hprecision : pGain + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target)
    (_hXiLog : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4 ≤ Plate),
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
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
    ∀ (hbases : bases.Nonempty),
    let hξn := normalizedTupleNarrowWidth_pos (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) Pphysical coarseTarget
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
    (s + 1) * (s + 3) ≤ Fintype.card G → (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect α) ≤ S.value →
    let budget := r.nativeBudget
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖

include hb o bW μ ν μrows hR hσ in
theorem preparedModularGeneralDirectDetectionFreeTrimInterface_of_geometry (hsm : s ≤ m)
    (Pchart D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ) (K : ℝ≥0)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B) (U := U) (basis := basis)
      (S := S) (nX := nX) Pchart P D target Pk Prho Qstride pDetect K) :
    PreparedModularGeneralDirectDetectionFreeTrimInterface
      (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τ)
      (hb := hb) (o := o)
      Pchart P D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget K := by
  intro hLate hMaster hDMaster hPkMaster hQstrideMaster hDetectMaster hnXMaster hRone
    hRiMaster hσiLate hSLate hKMaster hcutoffMaster hMkP hMkPk hstride hstrideBound
    C hC hCbound hchart Cforward hforward hForwardMaster hVtailMaster hVactual hBa hBi
    huMaster hModelMaster hSliceModel hcountModel hαlower hαone
    hPrhoMaster htargetMaster hGainMaster hCoarseMaster hCoarseLower hCoarseLate hPhysicalMaster hmPhysical hDimPhysical
    hvarsPhysical hXPhysical hPkPhysical hQstridePhysical hGainLog hprecision hXiLog
    hτSpatial hτinv r W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
  let constants := preparedModularGeneralDetectorConstants m s
  have hd := geometry.hdimensions
  have hmMaster : (m : ℝ) ≤ Pmaster := hd.degree.trans hDMaster
  have hJ := (allocatedProfile_dimensions U basis o B hd hb bW).1
  have hJMaster (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ Pmaster := (hJ j).trans hDMaster
  have hvarsMaster : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pmaster :=
    hvarsPhysical.trans hPhysicalMaster.2
  have hAsample : 2 ≤ constants.Asample :=
    (Classical.choose_spec (exists_allocatedCanonicalProjection_composed_budget m (s + 1)
      constants.Acover)).1
  have sampling := preparedModularGeneralDetector_sampling_bounds_of_geometry
    (J := J) stride B rowSets selection constants rfl hMaster hLate hAsample hd hDMaster
    hnXMaster (preparedModularGeneralDetector_ambient_count hJMaster) htargetMaster.2
    hPhysicalMaster.2 hQstrideMaster.2 hPkMaster.2 hstrideBound
  have freeSpatial := preparedModularGeneralDetector_free_spatial_bounds constants (s + 1)
    hMaster hLate hAsample hPhysicalMaster.2 hτSpatial hτinv
  have bounds := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget constants (s + 1))).2 hMaster hLate).1
  obtain ⟨hDn, hgridn, hvn, hFn, hBn, hPnative, hprimitiveNative⟩ :=
    preparedModularGeneralDetector_native_inputs constants (s + 1) hMaster hLate
  obtain ⟨_, _, hQlog, _, _, hFmodel⟩ :=
    preparedModularGeneralDetector_period_prefactor B U basis o hb bW hMaster hd hDMaster
      hnXMaster hPkMaster hQstrideMaster hDetectMaster ⟨hMaster, le_rfl⟩
  have hgrid := preparedModularGeneralDetector_grid_resource_width_bound constants (s + 1)
    hMaster hLate hDetectMaster hQlog
  have hEarlyCoarse : pGain + 32 ∈ Set.Icc 0 Pmaster :=
    ⟨by linarith only [hGainMaster.1], hCoarseMaster⟩
  have hCoarse0 : 0 ≤ coarseTarget := hEarlyCoarse.1.trans hCoarseLower
  have hAmbient := preparedModularGeneralDetector_ambient_bound constants (s + 1) hMaster
    (hd.outputs.trans hDMaster) ⟨bounds.Pbox.1, le_rfl⟩ hPrhoMaster
    ⟨bounds.Vlog.1, le_rfl⟩ ⟨bounds.Nlog.1, le_rfl⟩ ⟨bounds.Q.1, le_rfl⟩ htargetMaster
    ⟨bounds.baseAmbient.1, le_rfl⟩
  have hMkPhysical := hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)
  have hGPhysical : (Fintype.card G : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsPhysical
  obtain ⟨_, hXi⟩ := preparedModularDetector_narrow_width B selection hPhysicalMaster.1
    hCoarse0 hMkPhysical hDimPhysical hvarsPhysical hXPhysical
  have hXiProj : ξn⁻¹ ≤ Real.exp r.Pproj :=
    hXi.trans (Real.exp_le_exp.mpr (hXiLog.trans sampling.late_projection))
  have hRoot := preparedModularDetector_physical_root_of_variables B U basis S (hMaster.trans hLate)
    (hvarsMaster.trans hLate) hSLate
  have hRootLog : 2 * Plate + 8 ≤ r.Pproj := by
    change 2 * Plate + 8 ≤ 4 * (Plate + 8)^2
    nlinarith only [hMaster.trans hLate, sq_nonneg Plate]
  have hWproj : W ≤ Real.exp r.Pproj := hRoot.trans (Real.exp_le_exp.mpr hRootLog)
  have hExpProj : Real.exp Pmaster ≤ Real.exp r.Pproj :=
    Real.exp_le_exp.mpr sampling.primitive_projection
  have hGain := allocatedDetectedGain_lower s
    (Fintype.card (LayerSamplerVariables G I n B)) Pdetect hαlower hGainLog
  obtain ⟨hReqSample, hReqMass, hReqProj, hReqSide, _⟩ :=
    preparedModularGeneralDetector_required_bounds constants (s + 1) hMaster hLate
  have hSize (x : ℝ) (hx : x ≤ r.required) (i : Fin nX) : Real.exp x ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hx).trans (hNlarge i)
  have hRank (x : ℝ) (hx : x ≤ r.required) : Real.exp x ≤ Rrank :=
    (Real.exp_le_exp.mpr hx).trans hRankLarge
  have hNative := preparedModularGeneralDirectDetectionAmbient
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    hsm Pchart D target Pk Prho Qstride K geometry hLate hMaster hDMaster hPkMaster hQstrideMaster
    hDetectMaster hnXMaster hRone hRiMaster hSLate hKMaster hcutoffMaster
    hMkP hMkPk hstride hstrideBound C hC hCbound hchart Cforward hforward
    hForwardMaster hVtailMaster hVactual hBa hBi
    (Pproj := r.Pproj) (coarseTarget := coarseTarget) (Ecoarse := pGain + 32) (pGain := pGain)
    (τ := τ) (Pphysical := Pphysical) (Pnative := r.Pnative) (Pside := r.Pside)
    cells poly hp hmem
    (lossTarget := pGain + 32) (Psample := r.Psample) (Rrank := Rrank)
    (Sstride := Real.exp Qstride) (εsample := Real.exp (-target)) (ηsample := Real.exp (-target))
    hstride (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hτSpatial sampling.sample_nonneg
    sampling.X_sample sampling.frame_sample sampling.stride_scale_nonneg sampling.stride_scale_sample
    sampling.precision_pos freeSpatial.tau_sample sampling.epsilon_sample hstrideBound
    (hSize _ hReqSample) hrank (hRank _ hReqSample) sampling.precision_pos
    sampling.ambient_dimension_sample (by simpa only [Fintype.card_fin] using (hAmbient.2.2.trans sampling.ambient_sample))
    sampling.jet_sample sampling.eta_sample hPhysicalMaster.1 hMkPhysical hmPhysical hCoarse0
    hDimPhysical hGPhysical (by simpa only [Fintype.card_fin] using hXPhysical)
    hprecision le_rfl le_rfl
  have hNative := hNative
    (hMaster.trans hPnative) hDn
    (by change 0 ≤ _ ∧ _ ≤ _
        have hCgrid : constants.Cgrid = Classical.choose
            (exists_preparedModularCanonicalDetector_grid_parameters.{0} m (s + 1) canonicalTransitionLip) := rfl
        rw [← hCgrid]
        simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, one_add_one_eq_two]
          using And.intro hgrid.1 (hgrid.2.trans hgridn.2)) hvn
    (by change 0 ≤ _ ∧ _ ≤ _
        simpa only [add_assoc] using And.intro hFmodel.1 (hFmodel.2.trans hFn.2))
    (hprimitiveNative _ hPrhoMaster) (hprimitiveNative _ hPkMaster)
    (hprimitiveNative _ htargetMaster) hBn (hprimitiveNative _ hPhysicalMaster)
    (hprimitiveNative _ hEarlyCoarse) (hprimitiveNative _ hGainMaster)
    (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr hQstridePhysical))
    (by simpa only [one_div] using hτinv)
    hGain (by linarith only [hGainMaster.2, sampling.gain_projection]) hCoarseLower le_rfl le_rfl
    Cforward sampling.cover_base sampling.cover_sample sampling.mass_sample hforward hVactual
    sampling.X_mass sampling.frame_mass sampling.stride_mass freeSpatial.tau_mass
    (hSize _ hReqMass) (hRank _ hReqMass) sampling.ambient_dimension_mass sampling.jet_mass
    (hvarsPhysical.trans (by linarith only [Real.add_one_le_exp Pphysical]))
    sampling.projection_one (hmMaster.trans sampling.primitive_projection)
    ((hd.kernel_variables.trans hDMaster).trans sampling.primitive_projection)
    (hSLate.trans (Real.exp_le_exp.mpr sampling.late_projection)) sampling.period_projection sampling.variables_projection hWproj
    (fun j => (hRiMaster j).trans hExpProj) (fun j => (hσiLate j).trans (Real.exp_le_exp.mpr sampling.late_projection))
    (fun j => ((hd.coefficients j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (((preparedModularGeneralDetector_layer_axes B rowSets hd).1 j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (((preparedModularGeneralDetector_layer_axes B rowSets hd).2 j).trans hDMaster).trans sampling.primitive_projection)
    (fun j => (hJMaster j).trans sampling.primitive_projection) sampling.profile_projection
    (fun j => (hForwardMaster j).trans hExpProj) (fun j => (hVtailMaster j).trans hExpProj)
    sampling.X_projection sampling.frame_projection sampling.stride_projection freeSpatial.tau_projection
    hXiProj (hSize _ hReqProj) (hRank _ hReqProj)
  have hNative := hNative sampling.projection_side sampling.mass_side
    sampling.physical_side (hCoarseLate.trans sampling.late_side) (hSize _ hReqSide)
  intro hCells bases hbases hξn hmass htotal Path pathLaw sides Sites e
    Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hslices hdense hdimensionDetect hcomplexity hcap hGdetect hkernel budget
    signal hsignal hzero hdetected
  exact hNative hCells hbases hmass htotal Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hslices hdense hdimensionDetect hcomplexity hcap hGdetect hkernel
    huMaster.1 hModelMaster.1 hSliceModel hcountModel hαlower hαone signal hsignal hzero hdetected

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
variable (α τ : ℝ)
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

def PreparedModularGeneralDirectDetectionFreeTrimPreparedInterface
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
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
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
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
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
    ∀ (signal : (Fin nX → ℤ) → ℂ),
    (∀ t, ‖signal t‖ ≤ 1) → (∀ t, t ∉ integerBox N → signal t = 0) →
    α ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal →
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun t : integerBox N => t.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun t => signal t.val) (fun t => star (twistData.eval N poly t.val) * Fnative t)‖

end Consumer

theorem exists_preparedModularGeneralDirectDetectionLateFloorFreeTrim (m s : ℕ) (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Cresource := Classical.choose (exists_preparedModularGeneral_uniform_resource_budget m)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect)
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    let Cphysical := Classical.choose (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)
    ∃ C Cscale : ℕ, 2 ≤ C ∧ 2 ≤ Cscale ∧
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
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ}, 1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
      0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 geometryBudget ∧ Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog geometryBudget Qw +
            (1 + geometryBudget ^ 2) * Pmin) ∧
          (S.value : ℝ) ≤ Real.exp ((P + Qw + Pmin + Cscale) ^ Cscale) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
            (basis := basis) (S := S) (s := s) (nX := nX)
            Palloc Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
          (∀ lateTarget : ℝ, coarseTarget ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster sourceBudget geometryBudget Qw Pphysical lateTarget +
              (1 + geometryBudget ^ 2) * Pmin
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
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α → α ≤ 1 →
              PreparedModularGeneralDirectDetectionFreeTrimPreparedInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
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
  obtain ⟨C, hC, hsource⟩ := exists_preparedModularGeneralCanonicalLateFloorPhysicalSource m s Cdetect
  obtain ⟨Cscale, hCscale, hScaleBudget⟩ := exists_preparedModularGeneralLateFloorScale_budget C
  refine ⟨C, Cscale, hC, hCscale, ?_⟩
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
  intro Lmin Wscale Qw Pmin hWscale hQw hWQw hPmin hLmin J _ U basis Pscale
  obtain ⟨S, hScaleGeometry, hPkScale, hFloor, hSWitness, hgap, ⟨geometry⟩, hgainKernel⟩ :=
    hsampler Lmin hWscale hQw hWQw hPmin hLmin U basis
  have hGeometry0 : 0 ≤ geometryBudget := hModelGeometry.1.trans hModelGeometry.2
  have hScalePolynomial := hSWitness.trans (Real.exp_le_exp.mpr
    (hScaleBudget hP hQw hPmin hGeometry0 (hGeometryBudget.trans hTotalBudget)))
  refine ⟨S, hScaleGeometry, hPkScale, hFloor, hSWitness, hScalePolynomial,
    hgap, ⟨geometry⟩, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  have hAlloc0 : 0 ≤ Palloc := hP.trans hPalloc
  have hMaster : 0 ≤ sourceBudget := hPhysicalMaster.1.trans hPhysicalMaster.2
  have hLateTarget0 : 0 ≤ lateTarget := hCoarseMaster.1.trans hCoarseLower
  obtain ⟨_, hLateBase, hWitnessBase, hCoarseBase, hXiBase⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hMaster hGeometry0 hQw hPhysicalMaster.1 hLateTarget0
  have hFloorCost : 0 ≤ (1 + geometryBudget ^ 2) * Pmin := by positivity
  have hBaseLate : preparedModularGeneralDetectorLateMaster sourceBudget geometryBudget Qw Pphysical lateTarget ≤ Plate :=
    le_add_of_nonneg_right hFloorCost
  have hLate := hLateBase.trans hBaseLate
  have hWitnessLate : allocatedWitnessScaleLog geometryBudget Qw + (1 + geometryBudget ^ 2) * Pmin ≤ Plate :=
    add_le_add hWitnessBase (le_refl ((1 + geometryBudget ^ 2) * Pmin))
  have hCoarseLate := hCoarseBase.trans hBaseLate
  have hXiLate := hXiBase.trans hBaseLate
  obtain ⟨hNativeResource, hRequiredResource⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneral_uniform_resource_budget m)).2
      hMaster hLate ⟨s, Nat.lt_succ_of_le hs⟩
  refine ⟨hNativeResource, hRequiredResource, rfl, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ _ _ _ _ _ μrows _ _ _ _ Vtail α τfree hαlower hαone
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff hτfree hτfreeInv hτfreeHalf hτfreeDim
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
  obtain ⟨_, hSliceModel, _, _, _, _, _, hcountModel, _, _, _, _, _, _, _, _⟩ :=
    preparedModularCanonicalDetector_early_cap L Jalloc A hCoord hAlloc0 hnum hpSlice.1 hu.1
      R Vtail hRpos (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
  have hMk := (hgainKernel α hαlower).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect
      α : ℝ)
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
  intro r W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases hξn Z
  have hτInvMaster : τfree⁻¹ ≤ Real.exp sourceBudget :=
    hτfreeInv.trans (Real.exp_le_exp.mpr hPhysicalMaster.2)
  have hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect α)
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
      hτfree hτInvMaster hτfreeHalf hτfreeDim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have consumer := preparedModularGeneralDirectDetectionFreeTrimInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
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
    ⟨hu.1, hu.2.trans hPMaster⟩ hModelMaster hSliceModel hcountModel hαlower hαone
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster.2 hCoarseLower hCoarseLate hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision.le hXiLate hτfree hτfreeInv
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm
    budget'
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity hMk.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_detected_canonical_early_radius_free_trim_detection (m s : ℕ)
    (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {Bstruct pnum pSlice Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct → (nX : ℝ) ≤ Bstruct →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P Eextra : ℝ}, 0 ≤ u → Bstruct + u ≤ P → 0 ≤ Eextra →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog budget Qw + (1 + budget ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
            (∀ (selection : Fin (s + 1) ↪ G) (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < t)
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
              [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ)
              (Pmaster Plate pGain Pphysical coarseTarget : ℝ),
              PreparedModularGeneralDirectDetectionFreeTrimInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
                (Vtail := Vtail) (α := α) (τ := τfree) (hb := hb) (o := o)
                Bstruct Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
                (Real.toNNReal (Real.exp pRadius))) ∧
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
  intro Cdetect
  obtain ⟨C, hC, hearly⟩ :=
    exists_detected_canonical_early_radius_late_floor_source m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ Bstruct pnum pSlice Qstride nX hm hs hB hnum
    hvars hI hn hblocks hpSlice hQstride hnX A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hsource⟩ :=
    hearly (G := G) B hm hs hB hnum hvars hI hn hblocks hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P Eextra hu hmaster hExtra Pearly pModel pDetect aDetect gainLog target Pk F Tmod
    δ E η Prho Ptail K budget
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, hsamplers⟩ := hsource hu hmaster hExtra
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Lmin W Qw Pmin hW hQw hWexp hPmin hLmin J _ U basis Pscale
  obtain ⟨S, hPscale, hkScale, hfloor, hS, hwidth, ⟨geometry⟩, hgainKernel⟩ :=
    hsamplers Lmin hW hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPscale, hkScale, hfloor, hS, hwidth, ?_, hgainKernel⟩
  intro selection hRpos hσpos stride N _ Q _ hb o bW _ ν _ _ _ _ _ μ _ _ _ _ _ μrows
    _ _ _ _ Vtail α τfree Pmaster Plate pGain Pphysical coarseTarget
  exact preparedModularGeneralDirectDetectionFreeTrimInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (α := α) (τ := τfree)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hs Bstruct D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
    (Real.toNNReal (Real.exp pRadius)) geometry

theorem exists_detected_canonical_early_radius_free_trim_prepared (m s : ℕ)
    (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {Bstruct pnum pSlice Qstride : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) → (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct → (nX : ℝ) ≤ Bstruct →
      (∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) →
      (∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
        ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩)) →
      (s + 1) * (s + 3) ≤ Fintype.card G →
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        let Pscale := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog budget Qw + (1 + budget ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master budget Qw Pphysical lateTarget +
              (1 + budget ^ 2) * Pmin
            (∀ (selection : Fin (s + 1) ↪ G) (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < t)
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
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α → α ≤ 1 →
              PreparedModularGeneralDirectDetectionFreeTrimPreparedInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
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
  intro Cdetect Aearly
  obtain ⟨C, hC, hearly⟩ := exists_detected_canonical_early_radius_late_floor_source m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ Bstruct pnum pSlice Qstride nX hm hs hB hnum
    hvars hI hn hblocks hpSlice hQstride hnX hBa hBi hcapacity
    A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hsource⟩ :=
    hearly (G := G) B hm hs hB hnum hvars hI hn hblocks hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have huP : u ≤ P := (le_add_of_nonneg_left hB).trans hmaster
  obtain ⟨hPQ, hEarlyQ, _, _, _, _, hGainQ, hPkQ⟩ :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)).2
      (G := G) B hm hs hP ⟨hnum.1, hnum.2.trans hBP⟩ hvars hI hn hblocks
      ⟨hpSlice.1, hpSlice.2.trans hBP⟩ ⟨hu, huP⟩
      ⟨hQstride.1, hQstride.2.trans hBP⟩ (hnX.trans hBP)
  have hQearly0 : 0 ≤ Qearly := hP.trans hPQ
  have hPhysical0 : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPkQ.1, hQstride.1,
      Nat.cast_nonneg (α := ℝ) nX, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hExtra : 0 ≤ Eextra := by
    have herror := coefficientErrorSpatialLog_nonneg hPhysical0
    dsimp only [Eextra]
    linarith only [herror]
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, hsamplers⟩ := hsource hu hmaster hExtra
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWexp hPmin hLmin J _ U basis Pscale
  obtain ⟨S, hScaleGeometry, hPkScale, hFloor, hSWitness, hgap, ⟨geometry⟩, hgainKernel⟩ :=
    hsamplers Lmin hWscale hQw hWexp hPmin hLmin U basis
  refine ⟨S, hScaleGeometry, hPkScale, hFloor, hSWitness, hgap, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate selection hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail α τfree hαlower hαone
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff hτfree hτfreeInv hτfreeHalf hτfreeDim
  have hGeometry0 : 0 ≤ budget := hModel.1.trans hModel.2
  have hEarly0 : 0 ≤ Pearly := hP.trans hPEarly
  have hGeometryMaster : budget ≤ master := by
    dsimp only [master]
    linarith only [hPhysical0, hEarly0, hgain.1]
  have hPhysicalMaster : Pphysical ∈ Set.Icc 0 master := by
    refine ⟨hPhysical0, ?_⟩
    dsimp only [master]
    linarith only [hGeometry0, hEarly0, hgain.1]
  have hMaster : 0 ≤ master := hGeometry0.trans hGeometryMaster
  have hCoarseMaster : gainLog + 32 ≤ master := by
    dsimp only [master]
    linarith only [hGeometry0, hPhysical0, hEarly0]
  have hLateTarget0 : 0 ≤ lateTarget := by
    linarith only [hgain.1, hCoarseLower]
  obtain ⟨_, hLateBase, hWitnessBase, hCoarseBase, hXiBase⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hMaster hGeometry0 hQw hPhysical0 hLateTarget0
  have hFloorCost : 0 ≤ (1 + budget ^ 2) * Pmin := by positivity
  have hBaseLate : preparedModularGeneralDetectorLateMaster master budget Qw Pphysical lateTarget ≤ Plate :=
    le_add_of_nonneg_right hFloorCost
  have hLate := hLateBase.trans hBaseLate
  have hWitnessLate : allocatedWitnessScaleLog budget Qw + (1 + budget ^ 2) * Pmin ≤ Plate :=
    add_le_add hWitnessBase (le_refl ((1 + budget ^ 2) * Pmin))
  have hCoarseLate := hCoarseBase.trans hBaseLate
  have hXiLate := hXiBase.trans hBaseLate
  have liftMaster {x : ℝ} (hx : x ∈ Set.Icc 0 budget) : x ∈ Set.Icc 0 master :=
    ⟨hx.1, hx.2.trans hGeometryMaster⟩
  have hModelMaster := liftMaster hModel
  have hDetectMaster := liftMaster hDetect
  have hTargetMaster := liftMaster htarget
  have hDMaster := liftMaster hD
  have hGainMaster := liftMaster hgain
  have hPkMaster := liftMaster hPk
  have hPrhoMaster := liftMaster hPrho
  have hScaleMaster := liftMaster hScaleGeometry
  have hpRadiusMaster := hpRadiusBudget.trans hGeometryMaster
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hPMaster : P ≤ master := hPEarly.trans (hEarlyBudget.trans hGeometryMaster)
  have hBMaster := hBP.trans hPMaster
  have hExpMaster : Real.exp Bstruct ≤ Real.exp master := Real.exp_le_exp.mpr hBMaster
  obtain ⟨_, hSliceModel, _, hcountModel⟩ := detectedCanonicalEarlyRadiusModel_bounds
    (Fintype.card (LayerSamplerVariables G I n B)) hEarly0 hpSlice.1
    (hvars.trans (hnum.2.trans (hBP.trans hPEarly)))
  have hMk := (hgainKernel α hαlower).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect α : ℝ) ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr hPkScale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp master := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hpRadiusMaster
  have hQPhysical : Qearly ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hmPhysical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX]
  have hDimPhysical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical := by
    have hsm : (s : ℝ) ≤ m := Nat.cast_le.mpr hs
    dsimp only [Pphysical]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) nX, hsm]
  have hXPhysical : (nX : ℝ) ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hPkPhysical : Pk ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hQstride.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hQstridePhysical : Qstride ≤ Pphysical := by
    dsimp only [Pphysical]
    linarith only [hQearly0, hPk.1, Nat.cast_nonneg (α := ℝ) nX,
      Nat.cast_nonneg (α := ℝ) (m + 1)]
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    hvars.trans (hnum.2.trans (hBP.trans (hPQ.trans hQPhysical)))
  have hprecision : gainLog + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target := by
    dsimp only [target, Eextra]
    linarith only
  intro r W ξn hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases hξn Z
  have hτInvMaster : τfree⁻¹ ≤ Real.exp master :=
    hτfreeInv.trans (Real.exp_le_exp.mpr hPhysicalMaster.2)
  have hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect α) Pphysical lateTarget
  have hξInvLate : ξn⁻¹ ≤ Real.exp Plate :=
    (preparedModularDetector_narrow_width B selection hPhysical0 hLateTarget0
      (hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)) hDimPhysical hvarsPhysical hXPhysical).2.trans
      (Real.exp_le_exp.mpr hXiLate)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularGeneralDetector_late_positive_bounds B U basis S hb o μ ν hRpos hσpos
      (fun _ => htone) Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 hMaster hLate geometry.hdimensions
      hDMaster.2 (hnX.trans hBMaster)
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleMaster.2.trans hLate))) hSLate
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr (hQstride.2.trans hBMaster)))
      hτfree hτInvMaster hτfreeHalf hτfreeDim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have consumer := preparedModularGeneralDirectDetectionFreeTrimInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hs Bstruct D target Pk Prho Qstride master Plate gainLog Pphysical lateTarget
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer hLate hMaster hDMaster.2 hPkMaster
    ⟨hQstride.1, hQstride.2.trans hBMaster⟩ hDetectMaster (hnX.trans hBMaster)
    (fun j => (hR j).2.1)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleMaster.2.trans hLate)))
    hSLate hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk hstride hstrideBound
    Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual hBa hBi
    ⟨hu, huP.trans hPMaster⟩ hModelMaster hSliceModel hcountModel hαlower hαone
    hPrhoMaster hTargetMaster hGainMaster hCoarseMaster hCoarseLower hCoarseLate hPhysicalMaster
    hmPhysical hDimPhysical hvarsPhysical hXPhysical hPkPhysical hQstridePhysical
    (le_refl _) hprecision hXiLate hτfree hτfreeInv
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm budget'
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity hMk.2

end Erdos3.VectorPolynomial

end

end OAI
