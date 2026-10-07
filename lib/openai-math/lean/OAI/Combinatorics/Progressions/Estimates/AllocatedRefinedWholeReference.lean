/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.AllocatedLongResidueProfile

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim) grid sides
local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides
local notation "refined" => residueRefinedPeriod modulus q

noncomputable def allocatedRefinedWholeTerm
    (profile : frozenTuple → label → EuclideanJetLayers U O → ℂ)
    (y : fullTuple) : ℂ :=
  let u := principalAxisRestrict grid y
  let r := principalResidueLabel refined (principalAxisRestrict (fun a => ¬grid a) y)
  ∑ t : cells × window,
    allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
      reference N hW mesh base cells test u r t *
    profile u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q
      reference base cells u r t.1 t.2.val))

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedComplexReference_whole
    (profile : frozenTuple → label → EuclideanJetLayers U O → ℂ) :
    allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z profile =
    (whole).complexMean (allocatedRefinedWholeTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile) /
      (Z : ℂ) := by
  unfold allocatedRefinedComplexReference allocatedRefinedWholeTerm
  rw [principalTupleWeights_partition grid sides (allocatedPrincipalSides_pos B U b S)]
  simp only [principalAxisRestrict_join_left, principalAxisRestrict_join_right,
    FiniteProbabilityWeights.fiberLaw_complexMean]
  rfl

noncomputable def allocatedWholeProfileReferenceTerm
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℂ :=
  let u := principalAxisRestrict grid y
  let r := principalResidueLabel refined (principalAxisRestrict (fun a => ¬grid a) y)
  ∑ t : cells × window,
    allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
      reference N hW mesh base cells test u r t *
    profile y (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q
      reference base cells u r t.1 t.2.val))

noncomputable def allocatedWholeResidueProfile
    (profile : (∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) →
      AllocatedLongJetRows B U b S O → ℝ) (y : fullTuple) : EuclideanJetLayers U O → ℝ :=
  let u := principalAxisRestrict grid y
  let v := principalAxisRestrict (fun a => ¬grid a) y
  allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d
    (fun j _ => standardLatticeClosedQuarterBox (J j))
    (profile (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus))

omit [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedFamilyReference_whole
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hRefined : 0 < refined)
    (hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬grid a) sides a)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (hresidue : ∀ u r v,
      (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j)
    (profile : (∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) →
      AllocatedLongJetRows B U b S O → ℝ)
    (factor : EuclideanJetLayers U O → ℂ) :
    allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
      (fun u r z => (allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (profile (residue u r)) z : ℂ) * factor z) =
    (whole).complexMean (allocatedWholeProfileReferenceTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test
      (fun y z => (allocatedWholeResidueProfile B U b hR hσ S x rows modulus hb o bW d profile y z : ℂ) * factor z)) /
      (Z : ℂ) := by
  rw [allocatedRefinedComplexReference_whole]
  apply congrArg (fun z : ℂ => z / (Z : ℂ))
  apply (whole).complexMean_congr_support
  intro y hy
  let u := principalAxisRestrict grid y
  let v := principalAxisRestrict (fun a => ¬grid a) y
  let r := principalResidueLabel refined v
  have hlong : (long).weight v ≠ 0 := by
    have heq := principalTupleWeights_partition_weight grid sides
      (allocatedPrincipalSides_pos B U b S) y
    rw [heq] at hy
    exact (mul_ne_zero_iff.mp hy).2
  have hmass := principalResidueCell_mass_pos
    (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val)
    (principalAxisLength (fun a => ¬grid a) sides)
    (fun a => allocatedPrincipalSides_pos B U b S ⟨a.1.val, a.2⟩)
    refined hRefined r hsize
  have hcond : (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 := by
    have hlaw : allocatedLongResidueWeights B U b S refined hRefined r hsize =
        (long).condition (Finset.univ.filter (fun w => principalResidueLabel refined w = r)) hmass := by
      exact principalResidueWeights_eq_condition
        (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val)
        (principalAxisLength (fun a => ¬grid a) sides)
        (fun a => allocatedPrincipalSides_pos B U b S ⟨a.1.val, a.2⟩)
        refined hRefined r hsize
    rw [hlaw]
    change ((if v ∈ Finset.univ.filter (fun w => principalResidueLabel refined w = r)
      then (long).weight v else 0) /
        (long).mass (Finset.univ.filter (fun w => principalResidueLabel refined w = r))) ≠ 0
    have hv : v ∈ Finset.univ.filter (fun w => principalResidueLabel refined w = r) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, rfl⟩
    rw [ite_eq_left hv]
    exact div_ne_zero hlong hmass.ne'
  have hlabel : principalResidueLabel modulus (reference u r) = principalResidueLabel modulus v :=
    principalResidueLabel_eq_of_dvd _ _ ⟨∏ t, q t, rfl⟩ (href u r)
  have heq : allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) rows hb o bW d
      (fun j _ => standardLatticeClosedQuarterBox (J j)) (profile (residue u r)) =
      allocatedWholeResidueProfile B U b hR hσ S x rows modulus hb o bW d profile y := by
    unfold allocatedWholeResidueProfile
    change allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) rows hb o bW d
      (fun j _ => standardLatticeClosedQuarterBox (J j)) (profile (residue u r)) =
      allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (profile (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus))
    rw [show (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus) =
      residue u r from funext (hresidue u r v hcond)]
    exact allocatedCoveredProfileDensity_long_residue_eq B U b hR hσ S x rows hb o bW d
      u (reference u r) v modulus hperiod hlabel _
  unfold allocatedRefinedWholeTerm allocatedWholeProfileReferenceTerm
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (fun z : ℝ =>
    allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
      reference N hW mesh base cells test u r t * ((z : ℂ) * factor
        (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q
          reference base cells u r t.1 t.2.val)))) (congrFun heq _)

end Erdos3.VectorPolynomial

end

end OAI
