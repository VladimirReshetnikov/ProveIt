import OAI.Combinatorics.Progressions.Dynamics.PreparedFinalToleranceBudgets
import OAI.Combinatorics.Progressions.Estimates.SharedWidthPreparedLateToleranceFreeTrimSource

namespace OAI

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

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

def SharedWidthPreparedCenteredModelMarginalDataInterface
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
    ∀ {Pmarginal E : ℝ},
    0 ≤ Pmarginal → (m : ℝ) ≤ Pmarginal →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pmarginal →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmarginal →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pmarginal →
    Pchart ≤ Pmarginal → Qstride ≤ Pmarginal → Pphysical ≤ Pmarginal →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pmarginal) →
    (∀ j, (σ j)⁻¹ ≤ Real.exp Pmarginal) →
    (∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pmarginal) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pmarginal) →
    (∀ j, (n j : ℝ) ≤ Pmarginal) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pmarginal) →
    (S.value : ℝ) ≤ Real.exp Pmarginal →
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn) (hξle : ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget), ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    W ≤ Real.exp Pmarginal →
    ∀ (hξone : ξn ≤ 1), ξn⁻¹ ≤ Real.exp Pmarginal →
    let required := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
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
    0 < α →
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

include μ ν hR hσ hb o in

theorem sharedWidthPreparedCenteredModelMarginalData_of_direct
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    SharedWidthPreparedCenteredModelMarginalDataInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff Pmarginal E hPm hmSize hK hX hdim
    hChartPm hStridePm hPhysicalPm hRP hσP hcount hI hn hJ hLP hσone hsmall
    hτSpatial hτInv hτHalf hτDim r W ξn hξn hξle hξLate hW hWP hξone hξInv required
    cells poly hp hmem Rrank hsize hrank hRank V hCells bases Z
  have hsizeDirect (i) : Real.exp r.required ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans (hsize i)
  have hRankDirect : Real.exp r.required ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans hRank
  have hsizeMarginal (i) :
      Real.exp ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hsize i)
  have hRankMarginal :
      Real.exp ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m) ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans hRank
  have hCentered := preparedModularGeneralCenteredDetectionFreeTrimSharedWidth_of_direct
    B U basis hR hσ S selection stride N Pdetect u pModel pSlice Vtail α τ hb o μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hcenter, hweight, hdetect⟩ :=
    hCentered hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
      hξn hξle hξLate cells poly hp hmem hsizeDirect hrank hRankDirect hCells
  have hchartExp := Real.exp_le_exp.mpr hChartPm
  obtain ⟨_, _, _, _, _, hnormalizerCenter, hweightMarginal, hsite⟩ :=
    (preparedCenteredMarginalExponent_spec m).2 B U basis S hb o μ ν hR hσ hσone
      Cforward Vtail hforward hVactual C hC hchart hsmall
      hPm hmSize hK hX hdim hRP hσP hcount hI hn hJ
      (hprofile.trans hchartExp) hLP (fun j => (hForward j).trans hchartExp)
      (fun j => (hVtail j).trans hchartExp) poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr hStridePm))
      hW hWP hτSpatial (hτInv.trans (Real.exp_le_exp.mpr hPhysicalPm)) hτHalf
      (by simpa only [Fintype.card_fin] using hτDim) hξn hξone hξInv
      N hsizeMarginal hrank hRankMarginal cells hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path Zcenter
  refine ⟨hnormalizerCenter, ?_⟩
  intro centeredLaw
  refine ⟨hweight, ?_⟩
  intro pathLaw sides Sites e hrootSum physical
  let : Nonempty Sites := by
    have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
      cases k with
      | inl g => exact S.positive
      | inr j => exact allocatedPrincipalSides_pos B U basis S j
    let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
    exact (integerBox_nonempty sides).to_subtype
  constructor
  · exact hsite e (fun t k => (allocatedParameterBox_coordinate_bound B U basis S t k).trans hLP)
      (fun t => allocatedParameterBox_root_bound B U basis S t)
  · exact hdetect

def SharedWidthPreparedCenteredModelMarginalProjectionInterface
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
    ∀ {E : ℝ},
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn) (hξle : ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget), ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    let hξone : ξn ≤ 1 := hξle.trans (min_le_left _ _)
    let Pmarginal := r.Pproj
    let required := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
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
    0 < α →
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

include μ ν hR hσ hb o in

theorem sharedWidthPreparedCenteredModelMarginalProjectionData_of_direct
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    {D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hD : D ≤ Pmaster) (hnX : (nX : ℝ) ≤ Pmaster)
    (hChartMaster : Pchart ≤ Pmaster) (hStrideMaster : Qstride ≤ Pmaster)
    (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) (hσone : ∀ j, σ j ≤ 1) :
    SharedWidthPreparedCenteredModelMarginalProjectionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E hsmall hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal required
  have hbnd := preparedCenteredMarginalProjectionBounds B U basis S o hMaster hLate hd hD
    hnX hRP hσLate hLLate
  have h := sharedWidthPreparedCenteredModelMarginalData_of_direct
    B U basis hR hσ S selection stride N Pdetect u pModel pSlice Vtail α τ hb o ν μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
  exact h hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff hbnd.Pproj_nonneg hbnd.m_projection
    hbnd.variables_projection hbnd.X_projection hbnd.frame_projection
    (hChartMaster.trans hbnd.master_projection) (hStrideMaster.trans hbnd.master_projection)
    (hPhysicalMaster.trans hbnd.master_projection) hbnd.Rinv_projection hbnd.σinv_projection
    hbnd.coefficient_projection hbnd.I_projection hbnd.n_projection hbnd.J_projection
    hbnd.S_projection hσone hsmall hτSpatial hτInv hτHalf hτDim
    hξn hξle hξLate hbnd.root_projection hξone (hξLate.trans (Real.exp_le_exp.mpr hbnd.late_projection))

def SharedWidthPreparedCenteredModelMarginalRadiusInterface
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
    ∀ {E : ℝ},
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn) (hξle : ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget), ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    let hξone : ξn ≤ 1 := hξle.trans (min_le_left _ _)
    let Pmarginal := r.Pproj
    let required := max r.required ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
      preparedCenteredMarginalExponent m)
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
    0 < α →
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

omit [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [μ.IsAddLeftInvariant] in

theorem sharedWidthPreparedCenteredModelMarginalRadiusInterface_of_projection
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hProjection : SharedWidthPreparedCenteredModelMarginalProjectionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
    SharedWidthPreparedCenteredModelMarginalRadiusInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E
  exact hProjection hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff (E := E) (hsmall C hC hCbound)

end Consumer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

private theorem centeredSource_physical_bounds {Qearly Pk Qstride : ℝ} (nX m : ℕ)
    (hQ : 0 ≤ Qearly) (hPk : 0 ≤ Pk) (hs : 0 ≤ Qstride) :
    let physical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
    0 ≤ physical ∧ Pk ≤ physical ∧ (nX : ℝ) ≤ physical ∧
      (2 : ℝ) ≤ physical ∧ Qearly ≤ physical := by
  intro physical
  dsimp only [physical]
  have hn : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

private theorem centeredSource_master_bounds {budget physical early gain : ℝ}
    (hb : 0 ≤ budget) (hp : 0 ≤ physical) (he : 0 ≤ early) (hg : 0 ≤ gain) :
    let master := budget + physical + early + gain + 32
    budget ≤ master ∧ physical ≤ master ∧ 0 ≤ master := by
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem centeredSource_late_bounds {master seed Qw physical target Pmin scale : ℝ}
    (hm : 0 ≤ master) (hs : 0 ≤ seed) (hw : 0 ≤ Qw) (hp : 0 ≤ physical)
    (ht : 0 ≤ target) (hmin : 0 ≤ Pmin) (hscale : 0 ≤ scale) :
    let base := preparedModularGeneralDetectorLateMaster master seed Qw physical target
    let late := base + (1 + seed ^ 2) * Pmin + scale
    master ≤ late ∧
      allocatedWitnessScaleLog seed Qw + (1 + seed ^ 2) * Pmin ≤ late ∧
      scale ≤ late ∧
      2 * (spatialPrimitiveEnvelope physical target 0 +
        spatialTupleToleranceLog (spatialPrimitiveEnvelope physical target 0)) + 4 ≤ late := by
  intro base late
  obtain ⟨hb, hm', hw', _, hξ⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hm hs hw hp ht
  have hc : 0 ≤ (1 + seed ^ 2) * Pmin := mul_nonneg (by positivity) hmin
  dsimp only [late]
  exact ⟨by linarith only [hm', hc, hscale],
    by linarith only [hw', hscale], by linarith only [hb, hc],
    by linarith only [hξ, hc, hscale]⟩

def SharedWidthPreparedLateToleranceCenteredSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
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
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
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
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α / 2 → α ≤ 1 →
              SharedWidthPreparedCenteredModelMarginalRadiusInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) (μ := μ) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_sharedWidth_prepared_late_tolerance_centered_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    SharedWidthPreparedLateToleranceCenteredSourceStatement m Pdetect := by
  unfold SharedWidthPreparedLateToleranceCenteredSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_sharedWidth_prepared_late_tolerance_free_trim_source m Pdetect
  unfold SharedWidthPreparedLateToleranceFreeTrimSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWexp hPmin hLmin J _ U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hdetector, hgainKernel⟩ :=
    hsamplers Lmin hWscale hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  obtain ⟨hnative, hprepared⟩ := hdetector lateTarget hCoarseLower
  refine ⟨hnative, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail α τfree hαlower hαone
  have hDirect := hprepared hRpos hσpos stride N Q hb o bW ν μ μrows Vtail
    (α / 2) τfree hαlower (by linarith only [hαone])
  obtain ⟨hStruct, _, _, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  have hB : 0 ≤ Bstruct := hPstruct.trans hStruct
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have hQearly : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  obtain ⟨hPhysical0, _, hXPhysical, _, _⟩ :=
    centeredSource_physical_bounds nX m hQearly hPk.1 hQstride.1
  have hGeometry0 : 0 ≤ budget := hModel.1.trans hModel.2
  have hEarly0 : 0 ≤ Pearly := hP.trans hPEarly
  obtain ⟨hGeometryMaster, hPhysicalMaster, hMaster⟩ :=
    centeredSource_master_bounds hGeometry0 hPhysical0 hEarly0 hgain.1
  have hPMaster : P ≤ master := hPEarly.trans (hEarlyBudget.trans hGeometryMaster)
  have hBMaster := hBP.trans hPMaster
  have hLateTarget0 : 0 ≤ lateTarget := by linarith only [hgain.1, hCoarseLower]
  have hF : 0 ≤ F := by change 0 ≤ pDetect + 2; linarith only [hDetect.1]
  have hLength0 : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hSeedInput : 0 ≤ D + Pscale + lengthLog + 1 := by
    linarith only [hD.1, hScaleBound.1, hLength0]
  have hSeed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hSeedInput
  obtain ⟨hLate, hWitnessLate, hScaleLate, _⟩ :=
    centeredSource_late_bounds hMaster hSeed0 hQw hPhysical0 hLateTarget0 hPmin hScaleBound.1
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  apply sharedWidthPreparedCenteredModelMarginalRadiusInterface_of_projection
    B U basis hRpos hσpos S selection stride N Pdetect u pModel pSlice Vtail α τfree hb o μ
    Bstruct Qstride master Plate gainLog Pphysical lateTarget
  · exact sharedWidthPreparedCenteredModelMarginalProjectionData_of_direct
      B U basis hRpos hσpos S selection stride N Pdetect u pModel pSlice Vtail α τfree hb o ν μ
      Bstruct Qstride master Plate gainLog Pphysical lateTarget hDirect hMaster hLate
      hdimensions (hD.2.trans hGeometryMaster) (hXPhysical.trans hPhysicalMaster)
      hBMaster (hQstride.2.trans (hStruct.trans hBMaster)) hPhysicalMaster
      (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr (hpRadiusBudget.trans hGeometryMaster)))
      (fun _ => hσinv.trans (Real.exp_le_exp.mpr hScaleLate)) hSLate
      (fun _ => hσt.trans htone)
  · intro Cchart hCchart hCchartBound
    exact (hsmall Cchart hCchart hCchartBound).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def SharedWidthPreparedLateToleranceCertifiedSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
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
      ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {Pmin Elog Vlog : ℝ} (Qbad : ℕ),
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
        0 ≤ Elog → 0 ≤ Vlog → 1 ≤ Qbad → (Qbad : ℝ) ≤ Real.exp Vlog →
      let W := physicalBadProductGap (Jalloc * (nX + m * M)) Elog Vlog Qbad
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * Elog + 24
      let J := fun j : Fin m => (L j).Coord
      let Pbase := Bstruct + Pscale + pRadius
      let B0 := 1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ Bcert : ℝ, B0 ≤ Bcert →
            PreparedCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
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
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α / 2 → α ≤ 1 →
              SharedWidthPreparedCenteredModelMarginalRadiusInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) (μ := μ) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_sharedWidth_prepared_late_tolerance_certified_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    SharedWidthPreparedLateToleranceCertifiedSourceStatement m Pdetect := by
  classical
  unfold SharedWidthPreparedLateToleranceCertifiedSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_sharedWidth_prepared_late_tolerance_centered_source m Pdetect
  unfold SharedWidthPreparedLateToleranceCenteredSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨hStruct, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  have hBstruct : 0 ≤ Bstruct := hPstruct.trans hStruct
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Qσ hQσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Pmin Elog Vlog Qbad hPmin hLmin hElog hVlog hQbad hQexp W Qw J Pbase B0 U basis
  have hQw : 0 ≤ Qw := by dsimp only [Qw]; linarith only [hBstruct, hVlog, hElog]
  obtain ⟨hW, hWexp⟩ := preparedBadProductWitnessGap_bounds m nX M hnum.2
    hElog hVlog Qbad hQbad hQexp
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hdetector, hgainKernel⟩ :=
    hsamplers Lmin hW hQw hWexp hPmin hLmin U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hdetector, hgainKernel⟩
  have hF : 0 ≤ F := by change 0 ≤ pDetect + 2; linarith only [hDetect.1]
  have hLength : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hSeedInput : 0 ≤ D + Pscale + lengthLog + 1 := by
    linarith only [hD.1, hScaleBound.1, hLength]
  have hSeed : 0 ≤ Pseed := allocatedScaleLog_nonneg hSeedInput
  have hcert := preparedCertifiedSameScaleBadProductInterface_of_lateTolerance_larger
    (nX := nX) (M := M) (R := R) (σ := fun _ : Fin m => σ) L U basis S
    (Bstruct := Bstruct) (pRadius := pRadius) (Pscale := Pscale)
    (Elog := Elog) (Vlog := Vlog) (Pseed := Pseed) (Qw := Qw) (Pmin := Pmin) Qbad
    hBstruct hpRadius.1 hScaleBound.1 (hM.trans hStruct) (hnX.trans hStruct)
    (fun j => (hR j).2.2) (fun _ => hσinv)
    hSeed hQw hPmin hElog hVlog hQbad hQexp hm hCoord hSWitness hgap
  exact hcert

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def SharedWidthPreparedPerturbativeCertifiedSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {u P : ℝ}, 0 ≤ u → Bstruct + u ≤ P →
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
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
      ∀ {Ppert Epert : ℝ}, 0 ≤ Ppert → 0 ≤ Epert →
      let Qσ := fixedPathPerturbationLog D (D + Ppert + 4) Epert m
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {Pmin Elog Vlog : ℝ} (Qbad : ℕ),
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
        0 ≤ Elog → 0 ≤ Vlog → 1 ≤ Qbad → (Qbad : ℝ) ≤ Real.exp Vlog →
      let W := physicalBadProductGap (Jalloc * (nX + m * M)) Elog Vlog Qbad
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * Elog + 24
      let J := fun j : Fin m => (L j).Coord
      let Pbase := Bstruct + Pscale + pRadius
      let B0 := 1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ Bcert : ℝ, B0 ≤ Bcert →
            PreparedCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
          (∀ (Apert : ℝ≥0) {ηpert : ℝ}, 0 < ηpert →
            (Apert : ℝ) ≤ Real.exp Ppert → ηpert⁻¹ ≤ Real.exp Epert →
            let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
            let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
              (fun a => layerSamplerDegree I n a.val)
            σ * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
              slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
                m 1 (unitProfilePrincipalLowerBound B) (1 / 2) Apert ηpert) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
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
              (Vtail : Fin m → ℝ≥0) (α τfree : ℝ),
              Real.exp (-aDetect) ≤ α / 2 → α ≤ 1 →
              SharedWidthPreparedCenteredModelMarginalRadiusInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail) (α := α) (τ := τfree)
                (hb := hb) (o := o) (μ := μ) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_sharedWidth_prepared_perturbative_certified_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    SharedWidthPreparedPerturbativeCertifiedSourceStatement m Pdetect := by
  unfold SharedWidthPreparedPerturbativeCertifiedSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_sharedWidth_prepared_late_tolerance_certified_source m Pdetect
  unfold SharedWidthPreparedLateToleranceCertifiedSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro u P hu hmaster Pearly pModel pDetect aDetect gainLog Pk Qearly Pphysical Eextra target
    F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Ppert Epert hPpert hEpert Qσ σ Pscale lengthLog Pseed
  have hQσ : 0 ≤ Qσ := fixedPathPerturbationLog_nonneg hD.1
    (by linarith only [hD.1, hPpert]) hEpert m
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hQσ
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Pmin Elog Vlog Qbad hPmin hLmin hElog hVlog hQbad hQexp W Qw J Pbase B0 U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, hdetector, hgainKernel⟩ :=
    hsamplers Lmin Qbad hPmin hLmin hElog hVlog hQbad hQexp U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, ?_, hdetector, hgainKernel⟩
  intro Apert ηpert hηpert hApert hηinv
  exact allocatedPreparedFinalTolerance_chosen_tail (G := G) (D := D)
    (P := Ppert) (E := Epert) (t := t) B hD.1 hPpert hEpert
    hdimensions.tuples hdimensions.axes Apert hηpert hApert hηinv ht U basis S

end Erdos3.VectorPolynomial

end

end OAI
