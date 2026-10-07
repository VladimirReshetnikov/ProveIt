import OAI.Combinatorics.Progressions.Probability.AllocatedNormalizedConditionalHaar

namespace OAI

section

namespace Erdos3

theorem principalResidueLabel_eq_of_dvd {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ}
    (y y₀ : PrincipalIntegerTuples B h α L) {q refined : ℕ}
    (hdiv : q ∣ refined)
    (hlabel : principalResidueLabel refined y = principalResidueLabel refined y₀) :
    principalResidueLabel q y = principalResidueLabel q y₀ := by
  exact integerResidueMatrix_reduce (fun j i => (y j i : ℤ))
    (fun j i => (y₀ j i : ℤ)) hdiv hlabel

namespace VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

variable (u : PrincipalAxisTuples (B := B) (h := layerSamplerDegree I n) (α := α)
  (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v v₀ : PrincipalAxisTuples (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedCoveredProfileDensity_long_residue_eq (q : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hlabel : principalResidueLabel q v = principalResidueLabel q v₀)
    (f : AllocatedLongJetRows B U b S O → ℝ) :
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter f =
      allocatedCoveredProfileDensity B U b hR hσ S x u v₀ rows hb o bW d quarter f := by
  have hwhole : principalResidueLabel q (principalAxisJoin grid u v) =
      principalResidueLabel q (principalAxisJoin grid u v₀) := by
    rw [principalResidueLabel_join, principalResidueLabel_join, hlabel]
  have hgridless : allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f =
      allocatedGridlessCoveredProfile B U b S x u v₀ rows hb o bW d f := by
    have heq := allocatedWholeGridlessProfile_eq B U b S x
      (principalAxisJoin grid u v) (principalAxisJoin grid u v₀) rows hb o bW d q hperiod hwhole f
    simpa only [principalAxisRestrict_join_left, principalAxisRestrict_join_right] using heq
  have hgrid : allocatedGridJetDensity B U b hR hσ S x u v rows =
      allocatedGridJetDensity B U b hR hσ S x u v₀ rows := by
    funext z
    simp only [allocatedGridJetDensity_frozen_blocks B U b hR hσ S u rows]
  rw [allocatedCoveredProfileDensity_grid_multiplier,
    allocatedCoveredProfileDensity_grid_multiplier, hgrid, hgridless]

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedMaskedProfile_eq_whole_of_long_residue (q : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hlabel : principalResidueLabel q v₀ = principalResidueLabel q v)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod q))
    (hresidue : ∀ j, integerResidueMatrix
      (allocatedNonkernelJetMatrix B U b S x u rows j v) q = residue j)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    allocatedCoveredProfileDensity B U b hR hσ S x u v₀ rows hb o bW d quarter
      (allocatedLongProfileDensity B U b S x rows q residue f) =
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v) q f := by
  simp only [allocatedWholeMaskedCoveredProfile,
    principalAxisRestrict_join_left, principalAxisRestrict_join_right]
  rw [show (fun j => integerResidueMatrix
    (allocatedNonkernelJetMatrix B U b S x u rows j v) q) = residue from funext hresidue]
  exact allocatedCoveredProfileDensity_long_residue_eq B U b hR hσ S x rows hb o bW d
    u v₀ v q hperiod hlabel _

end VectorPolynomial
end Erdos3

end

end OAI
