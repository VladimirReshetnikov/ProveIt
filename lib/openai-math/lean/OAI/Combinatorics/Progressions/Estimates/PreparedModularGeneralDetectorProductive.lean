import OAI.Combinatorics.Progressions.Dynamics.PreparedModularProductivityBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorLateFloor
import OAI.Combinatorics.Progressions.Sampling.AllocatedFixedScaleProductiveNarrowSampler

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedModularGeneralProductivity_le_budget {P : ℝ} {A : ℕ}
    (hP : 0 ≤ P) (hA : 2 ≤ A) : P ≤ (P + A) ^ A := by
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 1 ≤ P + A := by linarith
  have hpower : P + A ≤ (P + A) ^ A := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤ A)
  exact (by linarith only [hAreal] : P ≤ P + A).trans hpower

theorem preparedModularGeneralProductivity_physical_bounds
    {Q Pk Qstride : ℝ} (m s nX : ℕ)
    (hQ : 0 ≤ Q) (hPk : 0 ≤ Pk) (hstride : 0 ≤ Qstride) (hs : s ≤ m) :
    let Phys := Q + Pk + Qstride + nX + (m + 1 : ℕ) + 8
    Q ≤ Phys ∧ ((s + 2 : ℕ) : ℝ) ≤ Phys ∧ (nX : ℝ) ≤ Phys ∧ Pk ≤ Phys := by
  have hsm : (s : ℝ) ≤ m := Nat.cast_le.mpr hs
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnX : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  dsimp only
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def preparedModularGeneralProductivityExponent (m : ℕ) : ℕ :=
  Classical.choose (exists_allocated_fixedScale_productive_joint_measure.{0,0,0,0,0,0} m)

 theorem preparedModularGeneralProductivityExponent_two_le (m : ℕ) :
    2 ≤ preparedModularGeneralProductivityExponent m :=
  (Classical.choose_spec (exists_allocated_fixedScale_productive_joint_measure.{0,0,0,0,0,0} m)).1

theorem preparedModularGeneral_productivity_bounds
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {Pmaster Plate Pprod D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hProd : 4 * (Plate + 8) ^ 2 ≤ Pprod)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnXpos : 0 < nX) (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pmaster)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pmaster)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : Fin nX → ℕ) (hs : ∀ d, 0 < stride d)
    (hsP : ∀ d, (stride d : ℝ) ≤ Real.exp Pmaster)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp Pmaster)
    (hτhalf : τ ≤ 1 / 2)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (N : Fin nX → ℕ) {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (hCells : cells.Nonempty) :
    (∀ d, Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ (N d : ℝ)) →
    Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ rank →
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    ∃ (_hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths (density center)),
    let law := fun center => selectedJointFiniteLaw bases
      (trimmedIntegerBox_nonempty N _ hmargin) stride cells widths hwidths hmass
      (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hD center)
    (∀ center,
      let Z := selectedJointDensityMass bases stride cells widths (density center)
      |Z - 1| ≤ Real.exp (-Pprod) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    ∀ (test : (Fin nX → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain → Real.exp (-Pprod) ≤ gain / 16 →
      12 * positiveProjectionAccuracy Pprod + 2 * (nX : ℝ) * τ ≤ gain / 8 →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite q.val (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q : Sites,
        jointIntegerPhysicalSite q.val (z.1.val,z.2.val) ∈ integerBox N := by
  intro hSize hRank W widths bases density sides Sites
  let : Nonempty (Fin nX) := ⟨⟨0, hnXpos⟩⟩
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLproj : Plate ≤ Pprod := by
    nlinarith only [hProd, hPlate, sq_nonneg Plate]
  have hExpLate := Real.exp_le_exp.mpr hLproj
  have hPproj : Pmaster ≤ Pprod := by
    nlinarith only [hProd, hPlate, hLate, sq_nonneg Plate]
  have h2Pproj : 2 * Pmaster ≤ Pprod := by
    nlinarith only [hProd, hPlate, hLate, sq_nonneg Plate]
  have hframeProj : (2 * Pmaster + 1) * Pmaster ≤ Pprod := by
    have hsq : Pmaster^2 ≤ Plate^2 := pow_le_pow_left₀ hMaster hLate 2
    nlinarith only [hProd, hPlate, hLate, hsq, sq_nonneg Plate]
  have hExp := Real.exp_le_exp.mpr hPproj
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * Pmaster :=
    (preparedModularGeneralDetector_variable_count B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd).trans (by linarith only [hD])
  have hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pprod := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul (add_le_add_left hvars 1) hnX (Nat.cast_nonneg _) (by positivity)).trans
      (by simpa only [add_comm] using hframeProj)
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ Pprod :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U basis o j)).trans
      (hd.axes.trans (hD.trans hPproj))
  have hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
  have hWproj : W ≤ Real.exp Pprod :=
    (preparedModularGeneralDetector_physical_root B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) U basis S hd (hD.trans hLate) hLLate).trans
        (Real.exp_le_exp.mpr (by nlinarith only [hProd, hPlate, hLate, sq_nonneg Plate]))
  have hProductive := (Classical.choose_spec
    (exists_allocated_fixedScale_productive_joint_measure.{0,0,0,0,0,0} m)).2
    (X := Fin nX) (G := G) B U basis S hb o μ ν hR hσ hσ1
    C V hC hV Cinv hCinv hchart hsmall
    (P := Pprod) (hMaster.trans hPproj) (hd.degree.trans (hD.trans hPproj))
    (hvars.trans h2Pproj) (by simpa only [Fintype.card_fin] using hnX.trans hPproj) hframe
    (fun j => (hRP j).trans hExp) (fun j => (hσLate j).trans hExpLate)
    (fun j => (hd.coefficients j).trans (hD.trans hPproj))
    (fun j => (hI j).trans (hD.trans hPproj)) (fun j => (hn j).trans (hD.trans hPproj)) hJ
    ((hd.profile.trans (hD.trans hPproj)).trans (by linarith [Real.add_one_le_exp Pprod]))
    (hLLate.trans hExpLate) (fun j => (hCP j).trans hExp) (fun j => (hVP j).trans hExp)
    p hp hm stride hs (fun d => (hsP d).trans hExp) hW hWproj
    hτ (hτP.trans hExp) hτhalf hξ hξ1 (hξLate.trans hExpLate) N hSize hrank hRank cells hCells
  obtain ⟨hN, hwidths, hmargin, hmass, hDens, hnormal, htest⟩ := hProductive
  refine ⟨hN, hwidths, hmargin, hmass, hDens, ?_⟩
  intro law
  refine ⟨hnormal, ?_⟩
  have hsides (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U basis S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hsides k).ne'⟩
  let : Nonempty Sites := (integerBox_nonempty sides).to_subtype
  intro test htestBound gain hgain hcollision hprecision hscore
  exact htest (Sites := Sites) Subtype.val Subtype.val_injective
    (fun q => allocatedParameterBox_root_bound B U basis S q)
    test htestBound gain hgain hcollision (by simpa only [Fintype.card_fin] using hprecision) hscore

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

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

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

def PreparedModularGeneralProductiveInterface
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ) : Prop :=
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
    let Pprod := r.Pproj
    let cutoff := max r.required ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m)
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
      (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j) {Rrank : ℝ},
    (∀ i, Real.exp cutoff ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp cutoff ≤ Rrank → cells.Nonempty →
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    ∃ (_hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths (density center)),
    let law := fun center => selectedJointFiniteLaw bases
      (trimmedIntegerBox_nonempty N _ hmargin) stride cells widths hwidths hmass
      (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center)
      (hD center)
    (∀ center,
      let Z := selectedJointDensityMass bases stride cells widths (density center)
      |Z - 1| ≤ Real.exp (-Pprod) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    (∀ center (c : ∀ j, U j),
      coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun a => c a.1))) →
      ∃ htotal : 0 < selectedJointDensityMass bases stride cells widths
        (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX)
          (fun j => subtractConstant (c j).val (poly j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))),
        allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX)
          (fun j => subtractConstant (c j).val (poly j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
          N _hN hW hτSpatial
          (normalizedTupleNarrowWidth_pos (Fin nX)
            (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
            (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
              Pdetect pDetect qDetect α) Pphysical coarseTarget)
          stride cells hmass bases (trimmedIntegerBox_nonempty N _ hmargin) htotal = law center ∧
        (∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (subtractConstant (c j).val (poly j))) ∧
        (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j)
          (subtractConstant (c j).val (poly j)))) ∧
    ∀ (test : (Fin nX → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, Real.exp (-pGain) ≤ gain →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite q.val (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S poly hmem c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q : Sites,
        jointIntegerPhysicalSite q.val (z.1.val,z.2.val) ∈ integerBox N

include ν

theorem preparedModularGeneralProductiveInterface_of_bounds
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hChartMaster : Pchart ≤ Pmaster) (hStrideMaster : Qstride ≤ Pmaster)
    {D : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hD : D ≤ Pmaster) (hnXpos : 0 < nX) (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster) (hσ1 : ∀ j, σ j ≤ 1)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate) (hLLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hPhysicalMaster : Pphysical ≤ Pmaster) (hτhalf : Real.exp (-Pphysical) ≤ 1 / 2)
    (hξLate : (∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart →
      (normalizedTupleNarrowWidth (Fin nX)
        (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
        (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
          Pdetect pDetect qDetect α) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate)
    (hGain : pGain ∈ Set.Icc 0 Pmaster)
    (hPhysical : pGain + (nX : ℝ) + 8 ≤ Pphysical) :
    PreparedModularGeneralProductiveInterface (B := B) (U := U) (basis := basis)
      (hR := hR) (hσ := hσ) (S := S) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (hb := hb) (o := o) (μ := μ) Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
    hprofile hcutoff r Pprod cutoff τ hτSpatial W ξn hW cells poly hp hmem Rrank
    hSize hrank hRank hCells widths bases density sides Sites
  have hτP : τ⁻¹ ≤ Real.exp Pmaster := by
    dsimp only [τ]
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr hPhysicalMaster
  have hξ := normalizedTupleNarrowWidth_pos (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect qDetect α) Pphysical coarseTarget
  have hξone := preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect qDetect α) Pphysical coarseTarget
  have hProdCutoff : (Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m ≤ cutoff := le_max_right _ _
  have hExpChart := Real.exp_le_exp.mpr hChartMaster
  obtain ⟨hN, hwidths, hmargin, hmass, hDensity, hnormal, htest⟩ :=
    preparedModularGeneral_productivity_bounds B U basis S hb o μ ν hR hσ hσ1
      Cforward Vtail hforward hVactual C hC hchart (hsmall C hC hCbound)
      (Pprod := Pprod) hMaster hLate le_rfl hd hD hnXpos hnX hRP hσLate hLLate
      (fun j => (hForward j).trans hExpChart) (fun j => (hVtail j).trans hExpChart)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr hStrideMaster))
      hτSpatial hτP hτhalf hξ hξone (hξLate hVtail hprofile) N hrank cells hCells
      (fun i => (Real.exp_le_exp.mpr hProdCutoff).trans (hSize i))
      ((Real.exp_le_exp.mpr hProdCutoff).trans hRank)
  refine ⟨hN, hwidths, hmargin, hmass, hDensity, ?_⟩
  intro law
  refine ⟨hnormal, ?_, ?_⟩
  · intro center c hc
    obtain ⟨htotal, heq⟩ := preparedModularGeneralCenteredLaw B U basis hb o hR hσ S
      poly hmem N hN hW hτSpatial hξ stride cells hmass bases
      (trimmedIntegerBox_nonempty N _ hmargin) center c hc (hDensity center)
    exact ⟨htotal, heq, preparedModularGeneralCentered_degree U poly hp c,
      preparedModularGeneralCentered_rank U poly (fun i => (N i : ℝ)) Rrank hrank c⟩
  · intro test htestBound gain hgain hscore
    have hPlate : 0 ≤ Plate := hMaster.trans hLate
    have hGainProd : pGain + 8 ≤ Pprod := by
      change pGain + 8 ≤ 4 * (Plate + 8) ^ 2
      nlinarith only [hGain.2, hLate, hPlate, sq_nonneg Plate]
    obtain ⟨hcollision, hprecision⟩ := preparedModularProductivity_precision nX
      hGain.1 hGainProd hPhysical hgain
    exact htest test htestBound gain ((Real.exp_pos _).trans_le hgain)
      hcollision hprecision hscore

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

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

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include ν

theorem preparedModularGeneralProductiveInterface_of_width_bounds
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hChartMaster : Pchart ≤ Pmaster) (hStrideMaster : Qstride ≤ Pmaster)
    {D : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hD : D ≤ Pmaster) (hnXpos : 0 < nX) (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster) (hσ1 : ∀ j, σ j ≤ 1)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate) (hLLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hPhysicalMaster : Pphysical ≤ Pmaster) (hτhalf : Real.exp (-Pphysical) ≤ 1 / 2)
    (hPhysical0 : 0 ≤ Pphysical) (hCoarse0 : 0 ≤ coarseTarget)
    (hDim : ((s + 2 : ℕ) : ℝ) ≤ Pphysical)
    (hVars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (hXPhysical : (nX : ℝ) ≤ Pphysical)
    (hXi : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4 ≤ Plate)
    (hMk : (∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart →
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect qDetect α : ℝ) ≤ Real.exp Pphysical)
    (hGain : pGain ∈ Set.Icc 0 Pmaster)
    (hPhysical : pGain + (nX : ℝ) + 8 ≤ Pphysical) :
    PreparedModularGeneralProductiveInterface (B := B) (U := U) (basis := basis)
      (hR := hR) (hσ := hσ) (S := S) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (hb := hb) (o := o) (μ := μ) Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  apply preparedModularGeneralProductiveInterface_of_bounds
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
    (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (hb := hb) (o := o) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    hMaster hLate hChartMaster hStrideMaster hd hD hnXpos hnX hRP hσ1 hσLate hLLate
    hsmall hPhysicalMaster hτhalf _ hGain hPhysical
  intro hVtail hprofile
  exact (preparedModularDetector_narrow_width B selection hPhysical0 hCoarse0
    (hMk hVtail hprofile) hDim hVars hXPhysical).2.trans (Real.exp_le_exp.mpr hXi)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators ContDiff NNReal Classical TensorProduct

theorem exists_preparedModularGeneralDetectorProductive (m s : ℕ) (Pdetect : Polynomial ℕ) :
    let Cdetect := sampledSupportedSlicedDetectionConstant s Pdetect
    let Cresource := Classical.choose (exists_preparedModularGeneral_uniform_resource_budget m)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    let Cgeom := Classical.choose (exists_detected_canonical_native_source_geometry.{0,0,0,0,0} m s Cdetect)
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m s Cdetect)
    let Cphysical := Classical.choose (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)
    let Aprod := preparedModularGeneralProductivityExponent m
    let Cprod := Classical.choose (exists_preparedModularProductivity_budget Aprod Cresource)
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
            max resources.required ((resources.Pproj + Aprod) ^ Aprod) ≤
              (sourceBudget + Plate + Cprod) ^ Cprod ∧
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
                (hb := hb) (o := o) Palloc Qstride sourceBudget Plate gainLog Pphysical lateTarget ∧
              (0 < nX → PreparedModularGeneralProductiveInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (hb := hb) (o := o) (μ := μ)
                Palloc Qstride sourceBudget Plate gainLog Pphysical lateTarget))) ∧
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
  intro Cdetect Cresource Aalloc Cgeom Aearly Cphysical Aprod Cprod
  obtain ⟨C, Cscale, hC, hCscale, hsource⟩ := exists_preparedModularGeneralDetectorLateFloor m s Pdetect
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
    hXiMaster, hExtra, hprecision, ?_⟩
  refine ⟨hτ, hτhalf, hτdim, hτinv, hcapacity, hkernelAllocation, hblockAllocation,
    hblockRows, hselection, houtputCount, hthreshold, ?_⟩
  refine ⟨pRadius, R, hpRadius, hpRadiusGeometry, hR, ?_⟩
  refine ⟨hModelGeometry, hDetectGeometry, haGeometry, hTargetGeometry, hDGeometry,
    hGainGeometry, hPkGeometry, hPrhoGeometry, hPtailGeometry, hTailCap, t, ht, htone, ?_⟩
  intro Lmin Wscale Qw Pmin hWscale hQw hWQw hPmin hLmin J _ U basis Pscale
  obtain ⟨S, hScaleGeometry, hPkScale, hFloor, hSWitness, hScalePolynomial, hgap, ⟨geometry⟩, hInterface, hgainKernel⟩ :=
    hsampler Lmin hWscale hQw hWQw hPmin hLmin U basis
  have hGeometry0 : 0 ≤ geometryBudget := hModelGeometry.1.trans hModelGeometry.2
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
  obtain ⟨hNativeResource, hRequiredResource, hNativeEq, hModelInterface⟩ := hInterface lateTarget hCoarseLower
  have hProductiveBudget := (Classical.choose_spec
    (exists_preparedModularProductivity_budget Aprod Cresource)).2
      hMaster (hMaster.trans hLate) hRequiredResource.2
  refine ⟨hNativeResource, hRequiredResource, hProductiveBudget, hNativeEq, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ _ _ _ _ _ μrows _ _ _ _ Vtail
  refine ⟨hModelInterface hRpos hσpos stride N Q hb o bW ν μ μrows Vtail, ?_⟩
  intro hnXpos
  have hCphysical : 2 ≤ Cphysical :=
    (Classical.choose_spec (exists_detectedCanonicalPhysicalBudget m Aearly Cgeom)).1
  have hAllocMaster : Palloc ≤ sourceBudget :=
    preparedModularGeneralProductivity_le_budget hAlloc0 hCphysical
  have liftMaster {x : ℝ} (hx : x ∈ Set.Icc 0 geometryBudget) : x ∈ Set.Icc 0 sourceBudget :=
    ⟨hx.1, hx.2.trans hGeometryBudget⟩
  have hDMaster := liftMaster hDGeometry
  have hGainMaster := liftMaster hGainGeometry
  have hPkMaster := liftMaster hPkGeometry
  have hScaleMaster := liftMaster hScaleGeometry
  have hpRadiusMaster := hpRadiusGeometry.trans hGeometryBudget
  have hSLate := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hPMaster : P ≤ sourceBudget := hPalloc.trans hAllocMaster
  have hMkPk (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Palloc)
      (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Palloc) : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect
      (allocatedModelUnitThreshold u pModel
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B)))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))) : ℝ)
      ≤ Real.exp Pk := (hgainKernel _ (hTailCap Vtail hVtail hprofile).2).2.1
  obtain ⟨hvarsEarly, hIEarly, hnEarly⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  obtain ⟨hAllocQ, hGainQ⟩ :=
    preparedModularGeneralProductivity_early_gain m s Cdetect (G := G) B hm hs hAlloc0 ⟨Nat.cast_nonneg _, hnum⟩ (Nat.cast_le.mpr hvarsEarly)
      (fun j => Nat.cast_le.mpr (hIEarly j)) (fun j => Nat.cast_le.mpr (hnEarly j))
      hblockRows ⟨hpSlice.1, hpSlice.2.trans hPalloc⟩ ⟨hu.1, hu.2.trans hPalloc⟩
      ⟨hQstride.1, hQstride.2.trans hPalloc⟩ (hnX.trans hPalloc)
  have hQearly0 : 0 ≤ Qearly := hAlloc0.trans hAllocQ
  obtain ⟨hQPhysical, hDimPhysical, hXPhysical, hPkPhysical⟩ :=
    preparedModularGeneralProductivity_physical_bounds m s nX hQearly0 hPkMaster.1 hQstride.1 hs
  have hvarsPhysical : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions L Jalloc hCoord).1).trans
      (hnum.trans (hAllocQ.trans hQPhysical))
  have hPhysicalGain : gainLog + (nX : ℝ) + 8 ≤ Pphysical :=
    preparedModularProductivity_physical_precision m nX hPkMaster.1 hQstride.1 hGainQ
  exact preparedModularGeneralProductiveInterface_of_width_bounds
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (hb := hb) (o := o) (μ := μ) (ν := ν)
    Palloc Qstride sourceBudget Plate gainLog Pphysical lateTarget
    hMaster hLate hAllocMaster (hQstride.2.trans hPMaster)
    geometry.hdimensions hDMaster.2 hnXpos (hnX.trans hPMaster)
    (fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr hpRadiusMaster))
    (fun _ => htone)
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr (hScaleMaster.2.trans hLate)))
    hSLate (fun C hC hCb => (geometry.hbudgets C hC hCb).1)
    hPhysicalMaster.2 hτhalf hPhysicalMaster.1 hLateTarget0
    hDimPhysical hvarsPhysical hXPhysical hXiLate
    (fun hV hprof => (hMkPk hV hprof).trans (Real.exp_le_exp.mpr hPkPhysical))
    hGainMaster hPhysicalGain

end Erdos3.VectorPolynomial

end

end OAI
