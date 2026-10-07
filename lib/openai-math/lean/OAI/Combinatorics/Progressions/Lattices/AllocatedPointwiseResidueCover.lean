/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueSitePrimitiveAverage

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq fullBooleanRowSetFintype

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
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedResidueCoverCoefficientMass : ℝ :=
  ((law).fiberLaw (principalResidueLabel q)).mean (fun r =>
    if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
      ∑ k, ‖coverSiteCoefficient (W ⟨r, hr⟩).expansion k‖
    else 0)

theorem allocatedResidueCoverCoefficientMass_le (C : ℝ)
    (h : ∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤ C) :
    allocatedResidueCoverCoefficientMass B U b S q W ≤ C := by
  let weights := (law).fiberLaw (principalResidueLabel q)
  apply (weights.mean_mono_on_support (g := fun _ => C) ?_).trans_eq (weights.mean_const C)
  intro r hr
  have hp : 0 < weights.weight r := lt_of_le_of_ne (weights.nonneg r) (Ne.symm hr)
  change 0 < ((law).fiberLaw (principalResidueLabel q)).weight r at hp
  rw [FiniteProbabilityWeights.fiberLaw_weight_eq_mass] at hp
  simpa only [dite_eq_left hp] using h ⟨r, hp⟩

noncomputable def allocatedSupportedIdealCoverValue
    (g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
      (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
    (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) : ℂ :=
  if hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
    let rr : AllocatedPositiveResidue (dim := dim) B U b S q := ⟨r, hr⟩
    allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q
        (W rr).representative (W rr).positive hb o bW
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
        (physicalCubeRowSample U d rows p hm v) *
      ∑ k, coverSiteCoefficient (W rr).expansion k * ∏ s,
        g rr k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
          (p a.1) a.2) / commonSitePeriod (W rr).expansion k : ℝ) : UnitAddCircle))
  else 0

theorem exists_allocated_ideal_residue_cover
    {Nt V Cc : activeAxes → ℝ} {L : ℝ≥0}
    (he : ∀ r a, ((W r).expansion a).Bounds (Nt a) (V a) (Cc a) L ((siteH) a))
    (Q : ℝ≥0) (hQ : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) (hσ1 : ∀ j, σ j ≤ 1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets C j) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod (W r).expansion k)
          (4 * commonSitePeriod (W r).expansion k)) (g r k s) ∧ ∀ v, ‖g r k s v‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedResidueCoverCoefficientMass B U b S q W ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
        ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            ((law).fiberLaw (principalResidueLabel q)).complexMean (fun r =>
              allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d
                (allocatedPhysicalLongIdeal B U b hR S rowSets δ) W r
                (physicalCubeRowSample U d rows p hm v)) =
            ((law).fiberLaw (principalResidueLabel q)).complexMean
              (allocatedSupportedIdealCoverValue B U b hR hσ S q W hb o bW d g δ x p hm v) := by
  have hlocal (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_ideal_physical_cover B U b hR hσ S d q
      (W r).representative (W r).positive hb o bW (W r).expansion (he r)
      Q hQ Cforward hforward K hK hσ1 C hC hchart hsmall
  choose g hg hc hv using hlocal
  refine ⟨g, hg, hc, allocatedResidueCoverCoefficientMass_le B U b S q W _ hc, ?_⟩
  intro δ hδ hδ1 x X p hp hm v
  apply congrArg ((law).fiberLaw (principalResidueLabel q)).complexMean
  funext r
  by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
  · simp only [allocatedSupportedResidueSiteProfile, allocatedSupportedIdealCoverValue, dite_eq_left hr]
    exact hv ⟨r, hr⟩ δ hδ hδ1 x p hp hm v
  · simp only [allocatedSupportedResidueSiteProfile, allocatedSupportedIdealCoverValue, dite_eq_right hr]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq fullBooleanRowSetFintype

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
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "law" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

theorem exists_allocated_ideal_residue_cover_pointwise
    {Nt V Cc : activeAxes → ℝ} {L : ℝ≥0}
    (he : ∀ r a, ((W r).expansion a).Bounds (Nt a) (V a) (Cc a) L ((siteH) a))
    (Q : ℝ≥0) (hQ : ∀ a : activeAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) (hσ1 : ∀ j, σ j ≤ 1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedIdealCoverRadius (G := G) B rowSets C j) :
    ∃ g : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        (∀ a, ((W r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ r k s, LipschitzWith (max (((Fintype.card activeAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod (W r).expansion k)
          (4 * commonSitePeriod (W r).expansion k)) (g r k s) ∧ ∀ v, ‖g r k s v‖ ≤ 1) ∧
      (∀ r, (∑ k, ‖coverSiteCoefficient (W r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) ∧
      allocatedResidueCoverCoefficientMass B U b S q W ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
        ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
          {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ)
            (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q),
            allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ) W r
              (physicalCubeRowSample U d rows p hm v) =
            allocatedSupportedIdealCoverValue B U b hR hσ S q W hb o bW d g δ x p hm v r := by
  have hlocal (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_ideal_physical_cover B U b hR hσ S d q
      (W r).representative (W r).positive hb o bW (W r).expansion (he r)
      Q hQ Cforward hforward K hK hσ1 C hC hchart hsmall
  choose g hg hc hv using hlocal
  refine ⟨g, hg, hc, allocatedResidueCoverCoefficientMass_le B U b S q W _ hc, ?_⟩
  intro δ hδ hδ1 x X p hp hm v r
  by_cases hr : 0 < (law).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))
  · simp only [allocatedSupportedResidueSiteProfile, allocatedSupportedIdealCoverValue, dite_eq_left hr]
    exact hv ⟨r, hr⟩ δ hδ hδ1 x p hp hm v
  · simp only [allocatedSupportedResidueSiteProfile, allocatedSupportedIdealCoverValue, dite_eq_right hr]

end Erdos3.VectorPolynomial

end

end OAI
