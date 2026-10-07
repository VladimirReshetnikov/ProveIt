/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.AllocatedProductRadiusBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedNormalizedIdealCover
import OAI.Combinatorics.Progressions.Estimates.AllocatedNormalizedProductCover
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridSpatialWeighted

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedClippedFullGridCoverCoefficientMass : ℝ :=
  ((law).fiberLaw (principalResidueLabel q)).mean (fun r =>
    if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
      ∑ k, ‖coverSiteCoefficient (W ⟨r, hr⟩).expansion k‖
    else 0)

theorem allocatedClippedFullGridCoverCoefficientMass_le (C : ℝ)
    (h : ∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤ C) :
    allocatedClippedFullGridCoverCoefficientMass B U b S q W ≤ C := by
  let weights := (law).fiberLaw (principalResidueLabel q)
  apply (weights.mean_mono_on_support (g := fun _ => C) ?_).trans_eq (weights.mean_const C)
  intro r hr
  have hp : 0 < weights.weight r := lt_of_le_of_ne (weights.nonneg r) (Ne.symm hr)
  change 0 < ((law).fiberLaw (principalResidueLabel q)).weight r at hp
  rw [FiniteProbabilityWeights.fiberLaw_weight_eq_mass] at hp
  simpa only [dite_eq_left hp] using h ⟨r, hp⟩

noncomputable def allocatedClippedFullGridCoverValue
    (g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
      (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
    (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) : ℂ :=
  if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
    let rr : AllocatedPositiveResidue (dim := dim) B U b S q := ⟨r, hr⟩
    allocatedClippedFullGridGlobalPrefactor B U b S rowSets d (allocatedIdealCoverSupport (G := G) B rowSets)
        x hb o bW q (W rr).representative
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
        (physicalCubeRowSample U d rows p hm v) *
      ∑ k, coverSiteCoefficient (W rr).expansion k * ∏ s,
        g rr k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
          (p a.1) a.2) / commonSitePeriod (W rr).expansion k : ℝ) : UnitAddCircle))
  else 0

theorem exists_allocated_clipped_full_grid_residue_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ r a, ((W r).expansion a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets C j) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod (W r).expansion k)
          (4 * commonSitePeriod (W r).expansion k)) (g r k s) ∧ ∀ v, ‖g r k s v‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedClippedFullGridCoverCoefficientMass B U b S q W ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
        ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            ∀ r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q,
              allocatedClippedFullGridResidueProfile B U b hR hσ S q x hb o bW d
                (allocatedPhysicalLongIdeal B U b hR S rowSets δ) W
                (allocatedIdealCoverSupport (G := G) B rowSets) r
                (physicalCubeRowSample U d rows p hm v) =
              allocatedClippedFullGridCoverValue B U b hR S q W hb o bW d g δ x p hm v r := by
  have hlocal (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_clipped_full_grid_ideal_cover B U b hR hσ S d q
      (W r).representative (W r).positive hb o bW (W r).expansion (he r)
      Q hQ Cforward hforward K hK C hC hchart hsmall
  choose g hg hc hv using hlocal
  refine ⟨g, hg, hc, allocatedClippedFullGridCoverCoefficientMass_le B U b S q W _ hc, ?_⟩
  intro δ hδ hδ1 x X p hp hm v r
  by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
  · simp only [allocatedClippedFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedClippedFullGridCoverValue, dite_eq_left hr]
    simpa only [allocatedClippedFullGridSiteProfile, allocatedFullGridResidueWitnessProfile] using
      hv ⟨r, hr⟩ δ hδ hδ1 x p hp hm v
  · simp only [allocatedClippedFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedClippedFullGridCoverValue, dite_eq_right hr, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

theorem exists_allocated_normalized_full_grid_residue_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ r a, ((W r).expansion a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets C j) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod (W r).expansion k)
          (4 * commonSitePeriod (W r).expansion k)) (g r k s) ∧ ∀ v, ‖g r k s v‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedClippedFullGridCoverCoefficientMass B U b S q W ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      (∀ r k s (u : ∀ j, euclideanSubspace (U j)) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w j))) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        g r k s (fun a => ((((u a.1).val a.2) / commonSitePeriod (W r).expansion k : ℝ) : UnitAddCircle)) =
          allocatedFullGridSiteFactor (G := G) B U b (R := R) (W r).expansion ig k s
            (fun a => ((w (ig a).1).2 (ig a).2 : ZMod (((W r).expansion a).period (k a))))
            (allocatedFullMixedSiteValue (R := R) U b w) / 2) ∧
      ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
        ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            ∀ r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q,
              allocatedClippedFullGridResidueProfile B U b hR hσ S q x hb o bW d
                (allocatedPhysicalLongIdeal B U b hR S rowSets δ) W
                (allocatedIdealCoverSupport (G := G) B rowSets) r
                (physicalCubeRowSample U d rows p hm v) =
              allocatedClippedFullGridCoverValue B U b hR S q W hb o bW d g δ x p hm v r := by
  have hlocal (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_normalized_full_grid_ideal_cover B U b hR hσ S d q
      (W r).representative (W r).positive hb o bW (W r).expansion (he r)
      Q hQ Cforward hforward K hK C hC hchart hsmall
  choose g hg hc hsite hv using hlocal
  refine ⟨g, hg, hc, allocatedClippedFullGridCoverCoefficientMass_le B U b S q W _ hc, hsite, ?_⟩
  intro δ hδ hδ1 x X p hp hm v r
  by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
  · simp only [allocatedClippedFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedClippedFullGridCoverValue, dite_eq_left hr]
    simpa only [allocatedClippedFullGridSiteProfile, allocatedFullGridResidueWitnessProfile] using
      hv ⟨r, hr⟩ δ hδ hδ1 x p hp hm v
  · simp only [allocatedClippedFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedClippedFullGridCoverValue, dite_eq_right hr, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uE uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type uE} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (δ : ℝ≥0)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "labelType" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius
  (allocatedProductIdealSiteRadius_pos B rowSets)
local notation "ideal" => allocatedPhysicalLongIdeal B U b hR S rowSets δ
local notation "rawProfile" => allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d ideal W

noncomputable def allocatedProductFullGridResidueProfile (r : labelType)
    (y : EuclideanJetLayers U (rowTypes)) : ℂ := cutoff y * rawProfile r y

noncomputable def allocatedProductFullGridWeightedError (weight : labelType → ℂ)
    (y : EuclideanJetLayers U (rowTypes)) : ℂ :=
  (law).complexMean (fun y₀ => weight (principalResidueLabel q y₀) *
    (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (rows) hb o bW d y₀ q ideal y : ℂ)) -
    ((law).fiberLaw (principalResidueLabel q)).complexMean (fun r => weight r *
      allocatedProductFullGridResidueProfile B U b hR hσ S q x hb o bW d W δ r y)

variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B
  (fun k : Fin m => boundedBooleanJetRows (Fin dim) (k.val + 1)) C j)
variable (hδ : 0 < δ) (hδ1 : δ ≤ 1)

include hσ1 hC hchart hsmall hδ hδ1 in
theorem allocatedProductFullGridWeightedError_eq (weight : labelType → ℂ)
    (y : EuclideanJetLayers U (rowTypes)) :
    allocatedProductFullGridWeightedError B U b hR hσ S q x hb o bW d W δ weight y =
      cutoff y * allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d ideal W weight y := by
  have hfix (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S)) :
      cutoff y * (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (rows) hb o bW d y₀ q ideal y : ℂ) =
        (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (rows) hb o bW d y₀ q ideal y : ℂ) := by
    exact allocatedProductSiteCutoff_fixes_source B U b S rowSets o hb bW d radius
      (allocatedProductIdealSiteRadius_pos B rowSets) hR hσ
      (allocatedIdealCoverSupport (G := G) B rowSets)
      (allocatedIdealCoverSupport_nonneg B rowSets) (allocatedIdealCoverSupport_inactive B rowSets)
      (allocatedProductIdealSiteRadius_dominates B rowSets) C hC hchart
      (allocatedProductGridRadius_source_budget B rowSets C hC (fun j => (hR j).le) hsmall)
      hσ1 x y₀ q ideal (allocatedPhysicalLongIdeal_cover_support B U b hR S rowSets δ hδ hδ1) y
  exact supportMask_weighted_complexMean_difference (law) ((law).fiberLaw (principalResidueLabel q))
    (principalResidueLabel q) weight
    (fun y₀ => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (rows) hb o bW d y₀ q ideal y : ℂ))
    (fun r => rawProfile r y) (cutoff y) hfix

include hσ1 hC hchart hsmall hδ hδ1 in
theorem allocatedProductFullGridWeightedError_norm (weight : labelType → ℂ)
    (y : EuclideanJetLayers U (rowTypes)) :
    ‖allocatedProductFullGridWeightedError B U b hR hσ S q x hb o bW d W δ weight y‖ ≤
      ‖allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d ideal W weight y‖ := by
  rw [allocatedProductFullGridWeightedError_eq B U b hR hσ S q x hb o bW d W δ
    hσ1 C hC hchart hsmall hδ hδ1, norm_mul]
  exact (mul_le_mul_of_nonneg_right (allocatedProductSiteCutoff_norm B U b S rowSets o hb bW d radius
    (allocatedProductIdealSiteRadius_pos B rowSets) y) (norm_nonneg _)).trans_eq (one_mul _)

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride))
variable (widths : Option (Fin dim) × X → ℝ) (hwidths : ∀ z, 0 < widths z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
variable (sample : (Option (Fin dim) × X → ℤ) → EuclideanJetLayers U
  (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)))
variable (weight : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
  (Option (Fin dim) × X → ℤ) → ℂ)

omit [DecidableEq X] in
include hσ1 hC hchart hsmall hδ hδ1 hwidths hZ in
theorem allocatedProductFullGridWeightedError_sampled {η : ℝ}
    (hraw : selectedResidueDensityMass stride cells widths (fun z =>
      ‖allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d ideal W
        (fun r => weight r z) (sample z)‖) ≤ η) :
    selectedResidueDensityMass stride cells widths (fun z =>
      ‖allocatedProductFullGridWeightedError B U b hR hσ S q x hb o bW d W δ
        (fun r => weight r z) (sample z)‖) ≤ η := by
  exact (selectedResidueDensityMass_mono stride cells widths hwidths hZ (fun z =>
    allocatedProductFullGridWeightedError_norm B U b hR hσ S q x hb o bW d W δ hσ1 C hC hchart hsmall
      hδ hδ1 (fun r => weight r z) (sample z))).trans hraw

omit [DecidableEq X] in
include hσ1 hC hchart hsmall hδ hδ1 in
theorem allocatedProductFullGridWeightedError_test {η : ℝ}
    (hraw : ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖∑' z, ((selectedResidueSmoothPMF stride cells widths hwidths hZ z).toReal : ℂ) *
        (allocatedFullGridWeightedProfileError B U b hR hσ S q x hb o bW d ideal W
          (fun r => weight r z) (sample z) * φ z)‖ ≤ η)
    (φ : (Option (Fin dim) × X → ℤ) → ℂ) (hφ : ∀ z, ‖φ z‖ ≤ 1) :
    ‖∑' z, ((selectedResidueSmoothPMF stride cells widths hwidths hZ z).toReal : ℂ) *
      (allocatedProductFullGridWeightedError B U b hR hσ S q x hb o bW d W δ
        (fun r => weight r z) (sample z) * φ z)‖ ≤ η := by
  have hcut (z : Option (Fin dim) × X → ℤ) : ‖cutoff (sample z) * φ z‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (allocatedProductSiteCutoff_norm B U b S rowSets o hb bW d radius
      (allocatedProductIdealSiteRadius_pos B rowSets) (sample z)) (norm_nonneg _)).trans
        (by simpa using hφ z)
  have h := hraw (fun z => cutoff (sample z) * φ z) hcut
  convert h using 1
  congr 1
  apply tsum_congr
  intro z
  rw [allocatedProductFullGridWeightedError_eq B U b hR hσ S q x hb o bW d W δ
    hσ1 C hC hchart hsmall hδ hδ1]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets

noncomputable def allocatedProductFullGridCoverValue
    (g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
      (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
    (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) : ℂ :=
  if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
    let rr : AllocatedPositiveResidue (dim := dim) B U b S q := ⟨r, hr⟩
    allocatedProductFullGridPrefactor B U b S rowSets d radius (allocatedProductIdealSiteRadius_pos B rowSets)
        x hb o bW q (W rr).representative
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
        (physicalCubeRowSample U d rows p hm v) *
      ∑ k, coverSiteCoefficient (W rr).expansion k * ∏ s,
        g rr k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
          (p a.1) a.2) / commonSitePeriod (W rr).expansion k : ℝ) : UnitAddCircle))
  else 0

theorem exists_allocated_product_full_grid_residue_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ r a, ((W r).expansion a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod (W r).expansion k)
          (4 * commonSitePeriod (W r).expansion k)) (g r k s) ∧ ∀ v, ‖g r k s v‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedClippedFullGridCoverCoefficientMass B U b S q W ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            ∀ r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q,
              allocatedProductFullGridResidueProfile B U b hR hσ S q x hb o bW d W δ r
                (physicalCubeRowSample U d rows p hm v) =
              allocatedProductFullGridCoverValue B U b hR S q W hb o bW d g δ x p hm v r := by
  have hlocal (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_product_full_grid_cover B U b hR hσ S d q
      (W r).representative (W r).positive hb o bW (W r).expansion (he r)
      Q hQ Cforward hforward K hK radius (allocatedProductIdealSiteRadius_pos B rowSets) C hC hchart
      (allocatedProductGridRadius_recovery_budget B rowSets C hC (fun j => (hR j).le) hsmall)
  choose g hg hc hv using hlocal
  refine ⟨g, hg, hc, allocatedClippedFullGridCoverCoefficientMass_le B U b S q W _ hc, ?_⟩
  intro δ x X p hp hm v r
  by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
  · simp only [allocatedProductFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedProductFullGridCoverValue, dite_eq_left hr]
    simpa only [allocatedProductFullGridProfile, allocatedFullGridResidueWitnessProfile] using
      hv ⟨r, hr⟩ x (allocatedPhysicalLongIdeal B U b hR S rowSets δ) p hp hm v
  · simp only [allocatedProductFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedProductFullGridCoverValue, dite_eq_right hr, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (q : ℕ) [NeZero q]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets

theorem exists_allocated_normalized_product_full_grid_residue_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ r a, ((W r).expansion a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod (W r).expansion k)
          (4 * commonSitePeriod (W r).expansion k)) (g r k s) ∧ ∀ v, ‖g r k s v‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedClippedFullGridCoverCoefficientMass B U b S q W ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      (∀ r k s (u : ∀ j, euclideanSubspace (U j)) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w j))) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        g r k s (fun a => ((((u a.1).val a.2) / commonSitePeriod (W r).expansion k : ℝ) : UnitAddCircle)) =
          allocatedFullGridSiteFactor (G := G) B U b (R := R) (W r).expansion ig k s
            (fun a => ((w (ig a).1).2 (ig a).2 : ZMod (((W r).expansion a).period (k a))))
            (allocatedFullMixedSiteValue (R := R) U b w) / 2) ∧
      ∀ (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            ∀ r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q,
              allocatedProductFullGridResidueProfile B U b hR hσ S q x hb o bW d W δ r
                (physicalCubeRowSample U d rows p hm v) =
              allocatedProductFullGridCoverValue B U b hR S q W hb o bW d g δ x p hm v r := by
  have hlocal (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_normalized_product_full_grid_cover B U b hR hσ S d q
      (W r).representative (W r).positive hb o bW (W r).expansion (he r)
      Q hQ Cforward hforward K hK radius (allocatedProductIdealSiteRadius_pos B rowSets) C hC hchart
      (allocatedProductGridRadius_recovery_budget B rowSets C hC (fun j => (hR j).le) hsmall)
  choose g hg hc hsite hv using hlocal
  refine ⟨g, hg, hc, allocatedClippedFullGridCoverCoefficientMass_le B U b S q W _ hc, hsite, ?_⟩
  intro δ x X p hp hm v r
  by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
  · simp only [allocatedProductFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedProductFullGridCoverValue, dite_eq_left hr]
    simpa only [allocatedProductFullGridProfile, allocatedFullGridResidueWitnessProfile] using
      hv ⟨r, hr⟩ x (allocatedPhysicalLongIdeal B U b hR S rowSets δ) p hp hm v
  · simp only [allocatedProductFullGridResidueProfile, allocatedSupportedFullGridResidueProfile,
      allocatedProductFullGridCoverValue, dite_eq_right hr, mul_zero]

end Erdos3.VectorPolynomial

end

end OAI
