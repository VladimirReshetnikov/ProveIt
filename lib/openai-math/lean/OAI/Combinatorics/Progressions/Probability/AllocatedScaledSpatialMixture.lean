/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.AllocatedBudgetedCutoffReference
import OAI.Combinatorics.Progressions.Dynamics.AllocatedCutoffWindowBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedAmbientBoxTests

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (period : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → ℕ)
variable [∀ r, NeZero (period r)]
variable {K : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → Type*}
variable [∀ r, Fintype (K r)]
variable (cI : ∀ r, K r → ℂ)
variable (fI : ∀ r, K r → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N q
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "spatialCap" => allocatedSpatialCoefficientCap X selection M modulus mesh
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (law) (principalResidueLabel refined)
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base

theorem allocatedRecenteredMaskedSpatialApproximation_mixed_error
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ r k s z, ‖fI r k s z‖ ≤ 1)
    (hrows : ∀ z, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H z)
    {T A ε ξ : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (href : ∀ cell : ColumnResiduePattern (Option (Fin dim)) X q,
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight q {cell} (referenceJetEnvelopeWidths q H) z,
        selectedResidueDensityMass q {cell} (referenceJetEnvelopeWidths q H)
          (fun z => amp * ‖cutoff (physicalCubeRowSample U d rows p hm
            (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ T)
    (herr : ∀ r, ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d (period r) radius positiveRadius hb o bW (cI r) (fI r) y‖ ≤ amp * A * (‖cutoff y‖ * ε)) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      let source := fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (reconstruct r a.val v) r
      let target := fun r : labels =>
        if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
            ∑ v ∈ spatialWindow H 4,
              allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
                coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm rr a
                (period rr) (cI rr) (fI rr) test v
        else 0
      ‖(residueLaw).complexMean source - (residueLaw).complexMean target‖ ≤
        (spatialCap * allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness) *
          (A * ε) * (factor * T) := by
  intro V test htest source target
  let e : labels → ℝ := fun r =>
    if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
      ∑ k, ‖coverSiteCoefficient (coverWitness ⟨r, hr⟩).expansion k‖ else 0
  let C := spatialCap * (A * ε) * (factor * T)
  have hV : ∀ z, 0 < V z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  have hlocal (r : labels) : ‖source r - target r‖ ≤ e r * C := by
    by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r))
    · let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
      dsimp only [source, target]
      simp only [dite_eq_left hr]
      apply finiteProbability_window_error (fun a : cells => selectedResidueCellWeight q cells V a)
        (fun a => selectedResidueCellWeight_nonneg q cells V a)
        (selectedResidueCellWeight_sum q cells V hV hZ) (spatialWindow H 4)
      intro a
      have h := allocatedRecenteredMaskedSpatialApproximation_window_error (τ := τ) B U b hR S X
        modulus q wholeReference coverWitness hb o bW d g δ x hM selection hx N hW mesh base cells
        p hm rr a (period rr) (cI rr) (fI rr) hq hN hτ hmesh hbudget hperiod hp (hg rr) (hfI rr)
        hrows hscale hA hε href (herr rr) test htest
      apply h.trans_eq
      simp only [e, dite_eq_left hr, C]
      ring
    · simp only [source, target, allocatedProductFullGridCoverValue, dite_eq_right hr,
        mul_zero, Finset.sum_const_zero, sub_self, norm_zero, e, zero_mul, le_refl]
  have h := (residueLaw).norm_complexMean_sub_le source target (fun r => e r * C) (fun r _ => hlocal r)
  apply h.trans_eq
  calc
    _ = (residueLaw).mean (fun r => C * e r) :=
      congrArg (residueLaw).mean (funext (fun r => mul_comm _ _))
    _ = C * (residueLaw).mean e := (residueLaw).mean_const_mul C e
    _ = _ := by change C * allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness = _; dsimp only [C]; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (period : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → ℕ)
variable [∀ r, NeZero (period r)]
variable {K : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → Type*}
variable [∀ r, Fintype (K r)]
variable (cI : ∀ r, K r → ℂ)
variable (fI : ∀ r, K r → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N q
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "spatialCap" => allocatedSpatialCoefficientCap X selection M modulus mesh
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (law) (principalResidueLabel refined)
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets radius *
  (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudgetRows : ∀ j, (Finset.card (boundedBooleanJetRows (Fin dim) (Fin.val j + 1)) + 1 : ℝ) *
  (Fintype.card (Finset (Fin dim)) * (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (allocatedProductIdealSiteRadius (G := G) B
      (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1)) : ℝ) * R j)))) ≤ 1 / 4)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (Vcov : Fin m → ℝ≥0) {Psrc Elog P : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S D Vcov Psrc)
variable (hVcov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vcov j)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P
local notation "uniformFactor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  ((Psrc + 1) ^ dim) ^ Fintype.card X)

include hσ1 hC hchart hbudgetRows hD hnum hVcov in
theorem allocatedRecenteredMaskedSpatialApproximation_budgeted_error
    {Ksample : ℕ}
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim Ksample rowTypes rows)
    (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Rrank S₀ εs η : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P)
    (hεs : 0 < εs) (hτP : 1 / τ ≤ Real.exp P) (hεsP : 1 / εs ≤ Real.exp P)
    (hstride : ∀ z, (q z : ℝ) ≤ S₀)
    (hsize : ∀ z, Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ (N z : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun z => (N z : ℝ)) Rrank (U j) (p j))
    (hRrank : Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ Rrank)
    (hη : 0 < η) (hElog : 0 ≤ Elog) (hηE : η⁻¹ ≤ Real.exp Elog)
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ r k s z, ‖fI r k s z‖ ≤ 1)
    (hrows : ∀ z, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H z)
    {A ε ξ : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (herr : ∀ r, ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d (period r) radius positiveRadius hb o bW (cI r) (fI r) y‖ ≤ amp * A * (‖cutoff y‖ * ε)) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      let source := fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (reconstruct r a.val v) r
      let target := fun r : labels =>
        if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
            ∑ v ∈ spatialWindow H 4,
              allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
                coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm rr a
                (period rr) (cI rr) (fI rr) test v
        else 0
      ‖(residueLaw).complexMean source - (residueLaw).complexMean target‖ ≤
        (spatialCap * allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness) *
          (A * ε) * (uniformFactor * (massCap + 2 * η + εs)) := by
  have href (cell : ColumnResiduePattern (Option (Fin dim)) X q) :=
    allocatedNormalizedCutoff_budgeted_reference_envelope (X := X) (J := J)
      B U b o S radius positiveRadius hR hσ1 C hC hchart rowSets hbudgetRows
      hb bW D hD Vcov hnum hVcov (allocatedProductIdealSiteRadius_one_le B rowSets)
      hSampling hP hn hdim μ ν p hp hm d q hq hS hSP hτ hεs hτP hεsP hstride
      N hsize hrank hRrank hη hElog hηE base cell
  intro V test htest source target
  have hmix := allocatedRecenteredMaskedSpatialApproximation_mixed_error (τ := τ)
    B U b hR S X modulus q wholeReference coverWitness hb o bW d g δ x hM selection hx
    N hW mesh base cells p hm period cI fI hq hN hτ hmesh le_rfl hperiod hp hg hfI
    hrows hscale hA hε hξ hZ href herr test htest
  apply hmix.trans
  have hratio : (1 + W) / (S.value : ℝ) ≤ Psrc + 1 := by
    simpa only [(allocatedPrimitiveRootRatio_bounds hnum.nonneg).1] using
      allocatedPhysicalRootBudget_zero_ratio B U b S hnum.nonneg hnum.variable_count
  have hratio0 : 0 ≤ (1 + W) / (S.value : ℝ) :=
    div_nonneg (add_nonneg zero_le_one hW) (Nat.cast_nonneg _)
  have hpow := pow_le_pow_left₀ hratio0 hratio dim
  have hfactor : factor ≤ uniformFactor :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (pow_nonneg hratio0 _) hpow (Fintype.card X))
      (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
  have hgrid : 0 ≤ allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness := by
    apply FiniteProbabilityWeights.mean_nonneg
    intro r
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · exact le_rfl
  have hspatial : 0 ≤ spatialCap := by
    have hcap := anisotropicSpatialDensityCap_nonneg selection
      (one_div_nonneg.mpr (Nat.cast_nonneg M))
    unfold allocatedSpatialCoefficientCap
    positivity
  have hmass : 0 ≤ massCap + 2 * η + εs := by
    have hcap : 0 ≤ allocatedUniformGridVolumeCap B rowSets radius :=
      zero_le_one.trans (allocatedUniformGridVolumeCap_one_le B rowSets radius)
    have hwindow : 0 ≤ (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) := by positivity
    exact add_nonneg (add_nonneg (mul_nonneg hcap hwindow)
      (mul_nonneg (by norm_num) hη.le)) hεs.le
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfactor hmass)
    (mul_nonneg (mul_nonneg hspatial hgrid) (mul_nonneg hA hε))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (period : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → ℕ)
variable [∀ r, NeZero (period r)]
variable {K : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → Type*}
variable [∀ r, Fintype (K r)]
variable (cI : ∀ r, K r → ℂ)
variable (fI : ∀ r, K r → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N q
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "spatialCap" => allocatedSpatialCoefficientCap X selection M modulus mesh
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (law) (principalResidueLabel refined)
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets radius *
  (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudgetRows : ∀ j, (Finset.card (boundedBooleanJetRows (Fin dim) (Fin.val j + 1)) + 1 : ℝ) *
  (Fintype.card (Finset (Fin dim)) * (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (allocatedProductIdealSiteRadius (G := G) B
      (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1)) : ℝ) * R j)))) ≤ 1 / 4)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (Vcov : Fin m → ℝ≥0) {Psrc Elog P : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S D Vcov Psrc)
variable (hVcov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vcov j)
variable {Pearly : ℝ} (hPearly : 0 ≤ Pearly)
variable (hvarsEarly : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pearly)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P
local notation "earlyFactor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  ((Pearly + 1) ^ dim) ^ Fintype.card X)

include hσ1 hC hchart hbudgetRows hD hnum hVcov hPearly hvarsEarly in
theorem allocatedRecenteredMaskedSpatialApproximation_early_budgeted_error
    {Ksample : ℕ}
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim Ksample rowTypes rows)
    (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Rrank S₀ εs η : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P)
    (hεs : 0 < εs) (hτP : 1 / τ ≤ Real.exp P) (hεsP : 1 / εs ≤ Real.exp P)
    (hstride : ∀ z, (q z : ℝ) ≤ S₀)
    (hsize : ∀ z, Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ (N z : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun z => (N z : ℝ)) Rrank (U j) (p j))
    (hRrank : Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ Rrank)
    (hη : 0 < η) (hElog : 0 ≤ Elog) (hηE : η⁻¹ ≤ Real.exp Elog)
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ r k s z, ‖fI r k s z‖ ≤ 1)
    (hrows : ∀ z, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H z)
    {A ε ξ : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (herr : ∀ r, ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d (period r) radius positiveRadius hb o bW (cI r) (fI r) y‖ ≤ amp * A * (‖cutoff y‖ * ε)) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      let source := fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (reconstruct r a.val v) r
      let target := fun r : labels =>
        if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
            ∑ v ∈ spatialWindow H 4,
              allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
                coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm rr a
                (period rr) (cI rr) (fI rr) test v
        else 0
      ‖(residueLaw).complexMean source - (residueLaw).complexMean target‖ ≤
        (spatialCap * allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness) *
          (A * ε) * (earlyFactor * (massCap + 2 * η + εs)) := by
  have href (cell : ColumnResiduePattern (Option (Fin dim)) X q) :=
    allocatedNormalizedCutoff_budgeted_reference_envelope (X := X) (J := J)
      B U b o S radius positiveRadius hR hσ1 C hC hchart rowSets hbudgetRows
      hb bW D hD Vcov hnum hVcov (allocatedProductIdealSiteRadius_one_le B rowSets)
      hSampling hP hn hdim μ ν p hp hm d q hq hS hSP hτ hεs hτP hεsP hstride
      N hsize hrank hRrank hη hElog hηE base cell
  intro V test htest source target
  have hmix := allocatedRecenteredMaskedSpatialApproximation_mixed_error (τ := τ)
    B U b hR S X modulus q wholeReference coverWitness hb o bW d g δ x hM selection hx
    N hW mesh base cells p hm period cI fI hq hN hτ hmesh le_rfl hperiod hp hg hfI
    hrows hscale hA hε hξ hZ href herr test htest
  apply hmix.trans
  have hratio : (1 + W) / (S.value : ℝ) ≤ Pearly + 1 := by
    simpa only [(allocatedPrimitiveRootRatio_bounds hPearly).1] using
      allocatedPhysicalRootBudget_zero_ratio B U b S hPearly hvarsEarly
  have hratio0 : 0 ≤ (1 + W) / (S.value : ℝ) :=
    div_nonneg (add_nonneg zero_le_one hW) (Nat.cast_nonneg _)
  have hpow := pow_le_pow_left₀ hratio0 hratio dim
  have hfactor : factor ≤ earlyFactor :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (pow_nonneg hratio0 _) hpow (Fintype.card X))
      (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
  have hgrid : 0 ≤ allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness := by
    apply FiniteProbabilityWeights.mean_nonneg
    intro r
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · exact le_rfl
  have hspatial : 0 ≤ spatialCap := by
    have hcap := anisotropicSpatialDensityCap_nonneg selection
      (one_div_nonneg.mpr (Nat.cast_nonneg M))
    unfold allocatedSpatialCoefficientCap
    positivity
  have hmass : 0 ≤ massCap + 2 * η + εs := by
    have hcap : 0 ≤ allocatedUniformGridVolumeCap B rowSets radius :=
      zero_le_one.trans (allocatedUniformGridVolumeCap_one_le B rowSets radius)
    have hwindow : 0 ≤ (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) := by positivity
    exact add_nonneg (add_nonneg (mul_nonneg hcap hwindow)
      (mul_nonneg (by norm_num) hη.le)) hεs.le
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfactor hmass)
    (mul_nonneg (mul_nonneg hspatial hgrid) (mul_nonneg hA hε))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (period : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → ℕ)
variable [∀ r, NeZero (period r)]
variable {K : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → Type*}
variable [∀ r, Fintype (K r)]
variable (cI : ∀ r, K r → ℂ)
variable (fI : ∀ r, K r → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N q
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "spatialCap" => allocatedSpatialCoefficientCap X selection M modulus mesh
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (law) (principalResidueLabel refined)
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets radius *
  (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable {Dgeom cgeom : ℝ}
variable (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim)
  (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type)) Dgeom)
variable (hcgeom : 0 ≤ cgeom)
variable (hIgeom : ∀ j, (Fintype.card (I j) : ℝ) ≤ Dgeom)
variable (hngeom : ∀ j, (n j : ℝ) ≤ Dgeom)
variable (hCgeom : ∀ j, C j ≤ Real.exp cgeom)
variable (hsmall : ∀ j, R j ≤ allocatedProductChartRadius m Dgeom cgeom)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (Vcov : Fin m → ℝ≥0) {Psrc Elog P : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S D Vcov Psrc)
variable (hVcov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vcov j)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P
local notation "uniformFactor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  ((Psrc + 1) ^ dim) ^ Fintype.card X)

include hσ1 hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall hD hnum hVcov in
theorem allocatedRecenteredMaskedSpatialApproximation_charted_error
    {Ksample : ℕ}
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim Ksample rowTypes rows)
    (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Rrank S₀ εs η : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P)
    (hεs : 0 < εs) (hτP : 1 / τ ≤ Real.exp P) (hεsP : 1 / εs ≤ Real.exp P)
    (hstride : ∀ z, (q z : ℝ) ≤ S₀)
    (hsize : ∀ z, Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ (N z : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun z => (N z : ℝ)) Rrank (U j) (p j))
    (hRrank : Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ Rrank)
    (hη : 0 < η) (hElog : 0 ≤ Elog) (hηE : η⁻¹ ≤ Real.exp Elog)
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ r k s z, ‖fI r k s z‖ ≤ 1)
    (hrows : ∀ z, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H z)
    {A ε ξ : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (herr : ∀ r, ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d (period r) radius positiveRadius hb o bW (cI r) (fI r) y‖ ≤ amp * A * (‖cutoff y‖ * ε)) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      let source := fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (reconstruct r a.val v) r
      let target := fun r : labels =>
        if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
            ∑ v ∈ spatialWindow H 4,
              allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
                coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm rr a
                (period rr) (cI rr) (fI rr) test v
        else 0
      ‖(residueLaw).complexMean source - (residueLaw).complexMean target‖ ≤
        (spatialCap * allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness) *
          (A * ε) * (uniformFactor * (massCap + 2 * η + εs)) := by
  have hbudgetRows := allocatedProductChartRadius_recovery_budget B rowSets hgeom hcgeom
    hIgeom hngeom C hC hCgeom (fun j => (hR j).le) hsmall
  exact allocatedRecenteredMaskedSpatialApproximation_budgeted_error
    B U b hR hσ1 S X modulus q wholeReference coverWitness hb o bW d g δ x hM selection hx
    N mesh base cells p hm period cI fI C hC hchart hbudgetRows D hD Vcov hnum hVcov
    hSampling hP hn hdim μ ν hS hSP hεs hτP hεsP hstride hsize hrank hRrank hη hElog hηE
    hq hN hτ hmesh hperiod hp hg hfI hrows hscale hA hε hξ hZ herr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

universe uX uJ

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (period : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → ℕ)
variable [∀ r, NeZero (period r)]
variable {K : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q) → Type*}
variable [∀ r, Fintype (K r)]
variable (cI : ∀ r, K r → ℂ)
variable (fI : ∀ r, K r → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N q
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "spatialCap" => allocatedSpatialCoefficientCap X selection M modulus mesh
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (law) (principalResidueLabel refined)
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets radius *
  (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable {Dgeom cgeom : ℝ}
variable (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim)
  (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type)) Dgeom)
variable (hcgeom : 0 ≤ cgeom)
variable (hIgeom : ∀ j, (Fintype.card (I j) : ℝ) ≤ Dgeom)
variable (hngeom : ∀ j, (n j : ℝ) ≤ Dgeom)
variable (hCgeom : ∀ j, C j ≤ Real.exp cgeom)
variable (hsmall : ∀ j, R j ≤ allocatedProductChartRadius m Dgeom cgeom)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (Vcov : Fin m → ℝ≥0) {Psrc Elog P : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S D Vcov Psrc)
variable (hVcov : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vcov j)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P
local notation "uniformFactor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  ((Psrc + 1) ^ dim) ^ Fintype.card X)

include hσ1 hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall hD hnum hVcov in
theorem allocatedRecenteredMaskedSpatialApproximation_scaled_error
    {Ksample : ℕ} (hKsample : 2 ≤ Ksample)
    (hSampling : PhysicalAmbientRowsKernelSampling.{uX, uJ, 0} m dim Ksample rowTypes rows)
    (hP : 0 ≤ P) (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Rrank S₀ εs η : ℝ} (hS : 0 ≤ S₀) (hSP : S₀ ≤ Real.exp P)
    (hεs : 0 < εs) (hτP : 1 / τ ≤ Real.exp P) (hεsP : 1 / εs ≤ Real.exp P)
    (hstride : ∀ z, (q z : ℝ) ≤ S₀)
    (hsize : ∀ z, Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ (N z : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun z => (N z : ℝ)) Rrank (U j) (p j))
    (hRrank : Real.exp ((Qbudget + Ksample) ^ Ksample) ≤ Rrank)
    (hη : 0 < η) (hElog : 0 ≤ Elog) (hηE : η⁻¹ ≤ Real.exp Elog)
    (hq : ∀ z, 0 < q z) (hτ : 0 < τ) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ r k s z, ‖fI r k s z‖ ≤ 1)
    {A ε ξ : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (herr : ∀ r, ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d (period r) radius positiveRadius hb o bW (cI r) (fI r) y‖ ≤ amp * A * (‖cutoff y‖ * ε)) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      let source := fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (reconstruct r a.val v) r
      let target := fun r : labels =>
        if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
            ∑ v ∈ spatialWindow H 4,
              allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
                coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm rr a
                (period rr) (cI rr) (fI rr) test v
        else 0
      ‖(residueLaw).complexMean source - (residueLaw).complexMean target‖ ≤
        (spatialCap * allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness) *
          (A * ε) * (uniformFactor * (massCap + 2 * η + εs)) := by
  have hwindow := allocatedCutoffSampling_physical_window (dim := dim)
    B U b S D Vcov hnum N q hKsample hElog hP hτ hτP hq
    (fun z => (hstride z).trans hSP) hsize
  exact allocatedRecenteredMaskedSpatialApproximation_charted_error
    B U b hR hσ1 S X modulus q wholeReference coverWitness hb o bW d g δ x hM selection hx
    N mesh base cells p hm period cI fI C hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall
    D hD Vcov hnum hVcov hSampling hP hn hdim μ ν hS hSP hεs hτP hεsP hstride
    hsize hrank hRrank hη hElog hηE hq (fun z => (hwindow z).1) hτ hmesh hperiod hp hg hfI
    (fun z => (hwindow z).2.1) (fun z => (hwindow z).2.2) hA hε hξ hZ herr

end Erdos3.VectorPolynomial

end

end OAI
