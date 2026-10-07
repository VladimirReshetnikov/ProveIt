import OAI.Combinatorics.Progressions.Estimates.AllocatedEarlyGenuineError
import OAI.Combinatorics.Progressions.Estimates.AllocatedEarlyGenuineSource
import OAI.Combinatorics.Progressions.Linear.AllocatedGenuineKernelBudget
import OAI.Combinatorics.Progressions.Probability.AllocatedProductCutoffMass
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridCoefficientBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

def allocatedGenuineComparisonErrorLog {A : Type*} [Semiring A]
    (m : ℕ) (P D c s O E : A) : A :=
  s + allocatedFullGridCoefficientPreLog m D O + allocatedGenuineKernelErrorLog m D P +
    coefficientErrorVolumeLog P + allocatedProductCutoffMassLog m D c + E + 1

theorem allocatedGenuineComparisonErrorLog_nonneg (m : ℕ) {P D c s O E : ℝ}
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hc : 0 ≤ c) (hs : 0 ≤ s) (hO : 0 ≤ O) (hE : 0 ≤ E) :
    0 ≤ allocatedGenuineComparisonErrorLog m P D c s O E := by
  have hkernel := allocatedGenuineKernelErrorLog_nonneg m hD hP
  have hmass := allocatedProductCutoffMassLog_nonneg m hD hc
  unfold allocatedGenuineComparisonErrorLog allocatedFullGridCoefficientPreLog coefficientErrorVolumeLog
  positivity

theorem exists_allocatedGenuineComparisonErrorLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {P D c s O E : ℝ},
      0 ≤ P → 0 ≤ D → 0 ≤ c → 0 ≤ s → 0 ≤ O → 0 ≤ E →
      allocatedGenuineComparisonErrorLog m P D c s O E ≤ (P + D + c + s + O + E + a) ^ a := by
  let poly : Polynomial ℕ := allocatedGenuineComparisonErrorLog m
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P D c s O E hP hD hc hs hO hE
  let T : ℝ := P + D + c + s + O + E
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hPT : P ≤ T := by dsimp [T]; linarith
  have hDT : D ≤ T := by dsimp [T]; linarith
  have hcT : c ≤ T := by dsimp [T]; linarith
  have hsT : s ≤ T := by dsimp [T]; linarith
  have hOT : O ≤ T := by dsimp [T]; linarith
  have hET : E ≤ T := by dsimp [T]; linarith
  have hmono : allocatedGenuineComparisonErrorLog m P D c s O E ≤
      allocatedGenuineComparisonErrorLog m T T T T T T := by
    unfold allocatedGenuineComparisonErrorLog allocatedFullGridCoefficientPreLog
      allocatedGenuineKernelErrorLog coefficientErrorVolumeLog allocatedProductCutoffMassLog
      allocatedCutoffMassLog allocatedIdealCoverInputLog allocatedSiteCoefficientLog
    gcongr
  apply hmono.trans
  simpa [poly, allocatedGenuineComparisonErrorLog, allocatedFullGridCoefficientPreLog,
    allocatedGenuineKernelErrorLog, coefficientErrorVolumeLog, allocatedProductCutoffMassLog,
    allocatedCutoffMassLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    Polynomial.eval₂_pow] using hpoly T hT

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]

local notation "refined" => residueRefinedPeriod modulus q
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "massCap" => (allocatedUniformGridVolumeCap B rowSets radius *
  (2 * ((2 : ℝ) ^ dim * (2 * (radius : ℝ))) + 1) ^
    Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)))

theorem allocatedGenuineComparison_error_bound
    {P D c s O E mesh Z η εs : ℝ} {M period : ℕ} (selection : Fin dim ↪ G)
    (hP : 0 ≤ P) (hDexp : D ≤ Real.exp P)
    (hdimP : ((dim + 1 : ℕ) : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ D)
    (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c)
    (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D)
    {T V Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (hgrid : ∀ r a, ((coverWitness r).expansion a).Bounds (T a) (V a) (Real.exp O) L (Hs a))
    (hO : 0 ≤ O) (hdim : dim ≤ m + 1) (hM : (M : ℝ) ≤ Real.exp P)
    (hperiod : period ≤ M ^ (m + 1))
    (hspatial : allocatedSpatialCoefficientCap X selection M modulus mesh ≤ Real.exp s)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hεs : 0 ≤ εs) (hεs1 : εs ≤ 1)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2) :
    (allocatedSpatialCoefficientCap X selection M modulus mesh *
        allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness *
      (((layerKernelIndexBound m M : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
          coefficientDeckPeriodCap rowTypes Kcov period) *
        Real.exp (-allocatedGenuineComparisonErrorLog m P D c s O E)) *
      (((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
          ((D + 1) ^ dim) ^ Fintype.card X) * (massCap + 2 * η + εs))) / Z ≤ Real.exp (-E) := by
  have hgrid0 : 0 ≤ allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness := by
    apply FiniteProbabilityWeights.mean_nonneg
    intro r
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · exact le_rfl
  have hgridBound := (allocatedFullGrid_coefficient_pre_bound B U b S refined coverWitness
    hgrid hO hdim hgeom.axes).2
  have hkernel0 : 0 ≤ (layerKernelIndexBound m M : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap rowTypes Kcov period :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (coefficientDeckPeriodCap_nonneg _ _ _)
  have hkernel := allocatedGenuineKernelError_exp_bound I n rowTypes Kcov hgeom.nonneg hP hM
    hperiod hgeom.degree hgeom.axes hgeom.rows hKcov
  have hmass0 : 0 ≤ massCap + 2 * η + εs := by
    have hcap : 0 ≤ allocatedUniformGridVolumeCap B rowSets radius :=
      zero_le_one.trans (allocatedUniformGridVolumeCap_one_le B rowSets radius)
    positivity
  have hmass : massCap + 2 * η + εs ≤ Real.exp (allocatedProductCutoffMassLog m D c) := by
    simpa only [Fintype.card_fin] using allocatedProductCutoffMass_exp_bound B rowSets
      hgeom hvars hc hI hn C hC hCc hη1 hεs1
  exact allocatedEarlyGenuineError_exp_bound dim X hgeom.nonneg hP hDexp hdimP hX
    hgrid0 hkernel0 hmass0 hspatial hgridBound hkernel hmass hZ hZi

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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
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
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)

local notation "refined" => residueRefinedPeriod modulus q
local notation "ig" => allocatedGridIntegerAxis B U b S
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
variable {Psp s O E Z : ℝ}
local notation "elog" => allocatedGenuineComparisonErrorLog m Psp Dgeom cgeom s O E
local notation "precision" => Real.exp (-elog)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P

include hσ1 hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall hD hnum hVcov in
theorem exists_allocated_budgeted_genuine_source_comparison
    (hPsp : 0 ≤ Psp) (hDexp : Dgeom ≤ Real.exp Psp)
    (hdimP : ((dim + 1 : ℕ) : ℝ) ≤ Psp) (hXP : (Fintype.card X : ℝ) ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Dgeom)
    (hKcov : ∀ j, (Fintype.card (Kcov j) : ℝ) ≤ Dgeom)
    (hs : 0 ≤ s) (hO : 0 ≤ O) (hE : 0 ≤ E) (hMP : (M : ℝ) ≤ Real.exp Psp)
    (hspatial : allocatedSpatialCoefficientCap X selection M modulus mesh ≤ Real.exp s)
    (hJoint : 0 < Z) (hJointInv : Z⁻¹ ≤ 2)
    {Nt Vg Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
      (a : {a // allocatedGridAxis (I := I) U b S.value a}),
      ((coverWitness r).expansion a).Bounds (Nt a) (Vg a) (Real.exp O) L (Hs a))
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
    (hη : 0 < η) (hη1 : η ≤ 1) (hεs1 : εs ≤ 1) (hElog : 0 ≤ Elog) (hηE : η⁻¹ ≤ Real.exp Elog)
    (hq : ∀ z, 0 < q z) (hτ : 0 < τ) (hmesh : 0 < mesh)
    (hmargin : 3 + 2 * mesh ≤ 4)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hdimSmall : dim ≤ m + 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ξ eδ : ℝ} (hξ : 0 < ξ)
    (heδ : 0 ≤ eδ)
    (hδexp : (δ : ℝ)⁻¹ ≤ Real.exp eδ)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z) :
    let _ : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
      (a : {a // allocatedGridAxis (I := I) U b S.value a}) (k : ((coverWitness r).expansion a).Term),
      NeZero (((coverWitness r).expansion a).period k) :=
      fun r a k => ⟨((hgrid r a).period_pos k).ne'⟩
    let normalizedMesh : ℝ≥0 := ⟨mesh, hmesh.le⟩
    ∃ t : Fin M, kernelPeriodCandidate (m + 1) t ≤ M ^ (m + 1) ∧
      ∃ F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
          (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin dim) I n,
      (∀ y₀, (F y₀).Bounds B U b S rowSets x y₀ refined d (kernelPeriodCandidate (m + 1) t)
        hb o bW hR δ precision (allocatedFiniteIdealInputLog m Dgeom eδ elog) (layerKernelIndexBound m M)) ∧
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      let source := fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))) r a v *
            allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d coverWitness δ r
              (physicalCubeRowSample U d rows p hm (reconstruct r a.val v))
      let target := fun r : labels =>
        if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
          ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
            ((integerBoxCubeCount N dim : ℂ) *
              𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
                allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
                  coverWitness hb o bW d x hM selection hx N hW normalizedMesh base cells p hm rr a
                  (kernelPeriodCandidate (m + 1) t) (F ((coverWitness rr).representative)).coefficient
                  (F ((coverWitness rr).representative)).factor test
                  ((physicalCubeParametersEquiv X dim).symm cube.val))
        else 0
      ‖(residueLaw).complexMean source / (Z : ℂ) -
          (residueLaw).complexMean target / (Z : ℂ)‖ ≤ Real.exp (-E) := by
  intro gridPeriod normalizedMesh
  have helog : 0 ≤ elog := allocatedGenuineComparisonErrorLog_nonneg m
    hPsp hgeom.nonneg hcgeom hs hO hE
  have hprecision : precision⁻¹ ≤ Real.exp elog := by
    simp only [Real.exp_neg, inv_inv, le_refl]
  obtain ⟨t, ht, F, hF, happrox⟩ :=
    exists_allocated_early_genuine_source_comparison
      (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (hσ1 := hσ1) (S := S)
      (X := X) (modulus := modulus) (q := q) (wholeReference := wholeReference)
      (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW) (d := d)
      (δ := δ) (x := x) (hM := hM) (selection := selection) (hx := hx) (N := N) (mesh := mesh)
      (base := base) (cells := cells) (p := p) (hm := hm) (C := C) (hC := hC) (hchart := hchart)
      (hgeom := hgeom) (hcgeom := hcgeom) (hIgeom := hIgeom) (hngeom := hngeom)
      (hCgeom := hCgeom) (hsmall := hsmall) (D := D) (hD := hD) (Vcov := Vcov)
      (hnum := hnum) (hVcov := hVcov) (hPearly := hgeom.nonneg) (hvarsEarly := hvars)
      hgrid hKsample hSampling hP hn hdim μ ν hS hSP hεs hτP hεsP hstride hsize hrank hRrank
      hη hElog hηE hq hτ hmesh hmargin hperiod hp hdimSmall hδ hδ1 (Real.exp_pos _) hξ
      heδ helog hδexp hprecision hZ
  refine ⟨t, ht, F, hF, ?_⟩
  intro V test htest source target
  have hraw := happrox test htest
  have herror := allocatedGenuineComparison_error_bound (Kcov := Kcov) (E := E)
    B U b S X modulus q coverWitness selection hPsp hDexp hdimP hXP hgeom hvars
    hcgeom hIgeom hngeom C hC hCgeom hKcov hgrid hO hdimSmall hMP ht hspatial
    hη.le hη1 hεs.le hεs1 hJoint hJointInv
  have hnorm : ‖(Z : ℂ)‖ = Z := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hJoint]
  rw [← sub_div, norm_div, hnorm]
  exact (div_le_div_of_nonneg_right hraw hJoint.le).trans herror

end Erdos3.VectorPolynomial

end

end OAI
