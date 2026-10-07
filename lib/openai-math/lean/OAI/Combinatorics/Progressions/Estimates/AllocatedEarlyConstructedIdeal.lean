import OAI.Combinatorics.Progressions.Probability.AllocatedEarlyScaledMixture

namespace OAI

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
variable {Pearly : ℝ} (hPearly : 0 ≤ Pearly)
variable (hvarsEarly : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pearly)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P
local notation "earlyFactor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  ((Pearly + 1) ^ dim) ^ Fintype.card X)

include hσ1 hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall hD hnum hVcov hPearly hvarsEarly in
theorem exists_allocated_early_spatial_ideal_approximation
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
    (hg : ∀ r k s u, ‖g r k s u‖ ≤ 1)
    (hdimSmall : dim ≤ m + 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε ξ eδ eε : ℝ} (hε : 0 < ε) (hξ : 0 < ξ)
    (heδ : 0 ≤ eδ) (heε : 0 ≤ eε)
    (hδexp : (δ : ℝ)⁻¹ ≤ Real.exp eδ) (hεexp : ε⁻¹ ≤ Real.exp eε)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z) :
    ∃ t : Fin M, kernelPeriodCandidate (m + 1) t ≤ M ^ (m + 1) ∧
      ∃ F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
          (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin dim) I n,
      (∀ y₀, (F y₀).Bounds B U b S rowSets x y₀ refined d (kernelPeriodCandidate (m + 1) t)
        hb o bW hR δ ε (allocatedFiniteIdealInputLog m Dgeom eδ eε) (layerKernelIndexBound m M)) ∧
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
                (kernelPeriodCandidate (m + 1) t) (F ((coverWitness rr).representative)).coefficient
                (F ((coverWitness rr).representative)).factor test v
        else 0
      ‖(residueLaw).complexMean source - (residueLaw).complexMean target‖ ≤
        (spatialCap * allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness) *
          (((layerKernelIndexBound m M : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
            coefficientDeckPeriodCap
              (fun j : Fin m => {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
              Kcov (kernelPeriodCandidate (m + 1) t)) * ε) * (earlyFactor * (massCap + 2 * η + εs)) := by
  obtain ⟨t, _, _, hfamily⟩ := exists_good_kernel_finite_ideal_family B U b S hR x hM selection hx
    hb o bW d hgeom hcgeom hIgeom hngeom C hC hchart hCgeom hsmall hdimSmall
    δ hδ hδ1 hε heδ heε hδexp hεexp
  obtain ⟨F, hF⟩ := hfamily refined
  refine ⟨t, kernelPeriodCandidate_le (m + 1) t, F, hF, ?_⟩
  let maskCap : ℝ := (layerKernelIndexBound m M : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
    coefficientDeckPeriodCap
      (fun j : Fin m => {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
      Kcov (kernelPeriodCandidate (m + 1) t)
  have hA : 0 ≤ maskCap := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (coefficientDeckPeriodCap_nonneg _ _ _)
  have hfI : ∀ r k s z, ‖(F ((coverWitness r).representative)).factor k s z‖ ≤ 1 :=
    fun r => (hF ((coverWitness r).representative)).2.2.2.1
  have herr := fun r => (hF ((coverWitness r).representative)).2.2.2.2.2.2.2.2.2.2
  exact allocatedRecenteredMaskedSpatialApproximation_early_scaled_error
    (K := fun r => (F ((coverWitness r).representative)).Term)
    B U b hR hσ1 S X modulus q wholeReference coverWitness hb o bW d g δ x hM selection hx
    N mesh base cells p hm (fun _ => kernelPeriodCandidate (m + 1) t)
    (fun r => (F ((coverWitness r).representative)).coefficient)
    (fun r => (F ((coverWitness r).representative)).factor)
    C hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall D hD Vcov hnum hVcov hPearly hvarsEarly
    hKsample hSampling hP hn hdim μ ν hS hSP hεs hτP hεsP hstride hsize hrank hRrank
    hη hElog hηE hq hτ hmesh hperiod hp hg hfI hA hε.le hξ hZ herr

end Erdos3.VectorPolynomial

end

end OAI
