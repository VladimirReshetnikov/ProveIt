/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueSitePrimitiveAverage
import OAI.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ)

local notation "tupleType" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S)
local notation "tuples" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "labelType" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S

structure AllocatedFullGridResidueWitness (r : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)) where
  representative : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
    (allocatedPrincipalSides B U b S)
  label_eq : principalResidueLabel q representative = r
  positive : 0 < (tuples).mass (Finset.univ.filter
    (fun y => principalResidueLabel q y = principalResidueLabel q representative))
  expansion : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim))

theorem exists_allocated_full_grid_residue_witnesses
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B (Fin dim) (fun j : Fin m => (rowSets j : Type)) D)
    (hα : Fintype.card (Fin dim) ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hq : 0 < q) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
    (hgamma : ∀ a : gridAxes, principalProfileSize (R (ig a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a).1 (ig a).2)) ≤ 1)
    (hσ1 : ∀ a : gridAxes, σ (ig a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : gridAxes, max
      (positiveModerateSpectrumBlockCount (ig a).1.val (rowSets (ig a).1).card
        ((layerTailDegree m + 2) * (rowSets (ig a).1).card))
      (uniformSpectrumBlockCount (ig a).1.val (rowSets (ig a).1).card
        (((ig a).1.val + 1) * (rowSets (ig a).1).card)) ≤
      Fintype.card (B ⟨(ig a).1, Sum.inr (ig a).2⟩)) :
    let O := allocatedMixedJointSiteLog m D p v (E + allocatedFullGridWindowLog D)
    ∃ W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val,
      ∀ r, (∀ a, ((W r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (z : AllocatedFrozenJetRows B U b S (rowTypes)),
        ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
          ((∏ a : gridAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q
            (principalResidueLabel q (W r).representative) (W r).positive a (z a)).toReal : ℝ) : ℂ) -
          allocatedFullGridSiteApproximation B U b S rowSets (W r).expansion z‖ ≤
            allocatedFullGridPointTolerance D δ := by
  have hreps (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    (tuples).exists_mem_positive_fiber (principalResidueLabel q) r.val r.property
  choose rep hrep using hreps
  have hc (r : AllocatedPositiveResidue (dim := dim) B U b S q) :
      0 < (tuples).mass (Finset.univ.filter
        (fun y => principalResidueLabel q y = principalResidueLabel q (rep r))) := by
    simpa only [hrep r] using r.property
  have hex (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_full_grid_site_approximation B U b hR hσ S rowSets q
      (principalResidueLabel q (rep r)) (hc r) hD hα hP hp hv hPp hq hqv
      (allocatedFullGridPointTolerance_pos (D := D) hδ)
      (add_nonneg hE (allocatedFullGridWindowLog_nonneg hD.nonneg))
      (allocatedFullGridPointTolerance_inv hδE) hsize hgamma hσ1 L hL hcP hsP hrows hB
  choose e hbounds herror using hex
  let W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val :=
    fun r => ⟨rep r, hrep r, hc r, e r⟩
  exact ⟨W, fun r => ⟨hbounds r, herror r⟩⟩

variable {r : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)}
variable (w : AllocatedFullGridResidueWitness (dim := dim) B U b S q r)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) ((Sigma.fst (Subtype.val a)).val + 1)}) → ℝ) → ℝ)

noncomputable def allocatedFullGridResidueWitnessProfile : EuclideanJetLayers U (rowTypes) → ℂ :=
  allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q
    w.representative w.positive f w.expansion

noncomputable def allocatedSupportedFullGridResidueProfile
    (W : (r : (AllocatedPositiveResidue (dim := dim) B U b S q)) → AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
    (r : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)) : EuclideanJetLayers U (rowTypes) → ℂ :=
  if hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
    allocatedFullGridResidueWitnessProfile B U b hR hσ S q (W ⟨r, hr⟩) x hb o bW d f
  else fun _ => 0

theorem allocatedSupportedFullGridResidueProfile_positive
    (W : (r : (AllocatedPositiveResidue (dim := dim) B U b S q)) → AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
    (r : (AllocatedPositiveResidue (dim := dim) B U b S q)) :
    allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f W r.val =
      allocatedFullGridResidueWitnessProfile B U b hR hσ S q (W r) x hb o bW d f := by
  unfold allocatedSupportedFullGridResidueProfile
  rw [dite_eq_left r.property]

theorem allocatedFullGridResidueWitnessProfile_error
    (hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
    (fun z => ((tuples).condition _ hr).complexMean (fun y =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)) -
      allocatedFullGridResidueWitnessProfile B U b hR hσ S q w x hb o bW d f z) =
    allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows) hb o bW d q
      w.representative w.positive (fun _ => True) f
      (allocatedFullGridSelectedApproximation B U b S rowSets w.expansion)
      (allocatedFullGridNaturalVolume B U b S rowSets) := by
  rcases w with ⟨y₀, hy₀, hcell, e⟩
  subst r
  simpa only [allocatedFullGridResidueWitnessProfile, FiniteProbabilityWeights.complexMean_ofReal] using
    allocatedFullGridSiteProfile_error B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e

theorem allocatedSupportedFullGridResidueProfile_error
    (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) → AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
    (r : AllocatedPositiveResidue (dim := dim) B U b S q) :
    (fun z => ((tuples).condition _ r.property).complexMean (fun y =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)) -
      allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f W r.val z) =
    allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows) hb o bW d q
      (W r).representative (W r).positive (fun _ => True) f
      (allocatedFullGridSelectedApproximation B U b S rowSets (W r).expansion)
      (allocatedFullGridNaturalVolume B U b S rowSets) := by
  rw [allocatedSupportedFullGridResidueProfile_positive]
  exact allocatedFullGridResidueWitnessProfile_error B U b hR hσ S q (W r) x hb o bW d f r.property

end Erdos3.VectorPolynomial

end

end OAI
