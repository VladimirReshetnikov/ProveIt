import OAI.Combinatorics.Progressions.Estimates.AllocatedEarlyConstructedIdeal

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
variable {Pearly : ℝ} (hPearly : 0 ≤ Pearly)
variable (hvarsEarly : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pearly)
local notation "Qbudget" => allocatedCutoffSamplingLog m dim Psrc (normalizedSiteCutoffBound : ℝ) Elog P
local notation "earlyFactor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  ((Pearly + 1) ^ dim) ^ Fintype.card X)

include hσ1 hC hchart hgeom hcgeom hIgeom hngeom hCgeom hsmall hD hnum hVcov hPearly hvarsEarly in
theorem exists_allocated_early_normalized_spatial_mixture
    {Nt Vg Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (hgrid : ∀ (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
      (a : {a // allocatedGridAxis (I := I) U b S.value a}),
      ((coverWitness r).expansion a).Bounds (Nt a) (Vg a) (Cc a) L (Hs a))
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
    (hdimSmall : dim ≤ m + 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε ξ eδ eε : ℝ} (hε : 0 < ε) (hξ : 0 < ξ)
    (heδ : 0 ≤ eδ) (heε : 0 ≤ eε)
    (hδexp : (δ : ℝ)⁻¹ ≤ Real.exp eδ) (hεexp : ε⁻¹ ≤ Real.exp eε)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
        (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s u, ‖g r k s u‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (coverWitness r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedClippedFullGridCoverCoefficientMass B U b S refined coverWitness ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      (∀ r k s (u : ∀ j, euclideanSubspace (U j)) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w j))) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        g r k s (fun a => ((((u a.1).val a.2) / commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle)) =
          allocatedFullGridSiteFactor (G := G) B U b (R := R) (coverWitness r).expansion ig k s
            (fun a => ((w (ig a).1).2 (ig a).2 : ZMod (((coverWitness r).expansion a).period (k a))))
            (allocatedFullMixedSiteValue (R := R) U b w) / 2) ∧
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
            allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d coverWitness δ r
              (physicalCubeRowSample U d rows p hm (reconstruct r a.val v))
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
  let Qsite : ℝ≥0 := ⟨8 * (Dgeom + 1), mul_nonneg (by norm_num) (by linarith [hgeom.nonneg])⟩
  have hQsite (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a).1 (ig a).2) : ℝ) + 1) ≤ Qsite := by
    have hc : ((layerIntegerPrincipalSlots (G := G) B (ig a).1 (ig a).2).card : ℝ) ≤ Dgeom :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hgeom.coefficients (ig a).1)
    change 8 * (_ + 1) ≤ 8 * (Dgeom + 1)
    linarith only [hc]
  let Kcover : ℝ≥0 := ⟨Real.exp Psrc, Real.exp_nonneg _⟩
  have hsmallCover (j : Fin m) : R j ≤ allocatedProductGridRadius (G := G) B rowSets C j :=
    (hsmall j).trans (allocatedProductChartRadius_le_charts B rowSets hgeom hcgeom hIgeom hngeom
      C hC hCgeom j).1
  obtain ⟨g, hg, hc, hmass, hsite, hcover⟩ :=
    exists_allocated_normalized_product_full_grid_residue_cover B U b hR hσ S refined coverWitness
      hb o bW d hgrid Qsite hQsite D hD Kcover hnum.radius_inv C hC hchart hsmallCover
  have hgn : ∀ r k s u, ‖g r k s u‖ ≤ 1 := fun r k s => (hg r k s).2
  refine ⟨g, hgn, hc, hmass, hsite, ?_⟩
  obtain ⟨t, ht, F, hF, happrox⟩ :=
    exists_allocated_early_spatial_ideal_approximation
      (B := B) (U := U) (b := b) (hR := hR) (hσ1 := hσ1) (S := S)
      (X := X) (modulus := modulus) (q := q) (wholeReference := wholeReference)
      (coverWitness := coverWitness) (hb := hb) (o := o) (bW := bW) (d := d) (g := g)
      (δ := δ) (x := x) (hM := hM) (selection := selection) (hx := hx) (N := N) (mesh := mesh)
      (base := base) (cells := cells) (p := p) (hm := hm) (C := C) (hC := hC) (hchart := hchart)
      (hgeom := hgeom) (hcgeom := hcgeom) (hIgeom := hIgeom) (hngeom := hngeom)
      (hCgeom := hCgeom) (hsmall := hsmall) (D := D) (hD := hD) (Vcov := Vcov)
      (hnum := hnum) (hVcov := hVcov) (hPearly := hPearly) (hvarsEarly := hvarsEarly)
      hKsample hSampling hP hn hdim μ ν hS hSP hεs hτP hεsP hstride hsize hrank hRrank
      hη hElog hηE hq hτ hmesh hperiod hp hgn hdimSmall hδ hδ1 hε hξ heδ heε hδexp hεexp hZ
  refine ⟨t, ht, F, hF, ?_⟩
  intro V test htest
  have hsource :
      (fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r a v *
            allocatedProductFullGridResidueProfile B U b hR hσ S refined x hb o bW d coverWitness δ r
              (physicalCubeRowSample U d rows p hm (reconstruct r a.val v))) =
      (fun r : labels => ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ spatialWindow H 4,
          allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (reconstruct r a.val v) r) := by
    funext r
    apply Finset.sum_congr rfl
    intro a _
    apply congrArg (fun z : ℂ => (selectedResidueCellWeight q cells V a : ℂ) * z)
    apply Finset.sum_congr rfl
    intro v _
    rw [hcover δ x p hp hm (reconstruct r a.val v) r]
  change ‖(residueLaw).complexMean _ - (residueLaw).complexMean _‖ ≤ _
  rw [hsource]
  exact happrox test htest

end Erdos3.VectorPolynomial

end

end OAI
