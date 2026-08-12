import PolynomialFormulas.LazardInvariantGradedReynolds

/-!
# The sharp nonmodular invariant-basis construction

This module isolates the general Reynolds-basis construction from the
computational modular counterexample.  For a finite permutation subgroup,
nonvanishing of its order in the ground field is exactly the hypothesis used
to invert the averaging denominator.  No orbit-count computation is part of
this dependency.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample

open scoped BigOperators
open Finset MvPolynomial

set_option autoImplicit false

open LazardInvariantModule
open LazardInvariantProjectionBlocks
open LazardInvariantArtinBasis
open LazardInvariantArtinModuleBasis
open LazardInvariantHomogeneousCoordinates
open LazardInvariantFiniteDegreeInduction
open LazardInvariantGradedReynolds

noncomputable section

variable (K : Type*) [Field K]
variable (n : ℕ)
variable (H : Subgroup (Equiv.Perm (Fin n))) [Fintype H]

/-- In a field, nonvanishing of the subgroup order is exactly what is needed
to construct the Reynolds averaging scalar. -/
@[reducible] def symmetricCardInvertibleOfNeZero
    (hcard : (Fintype.card H : K) ≠ 0) :
    Invertible (Fintype.card H : SymmetricRing K (Fin n)) where
  invOf := algebraMap K (SymmetricRing K (Fin n))
    (Fintype.card H : K)⁻¹
  invOf_mul_self := by
    change algebraMap K (SymmetricRing K (Fin n))
        (Fintype.card H : K)⁻¹ *
      algebraMap K (SymmetricRing K (Fin n))
        (Fintype.card H : K) = 1
    rw [← map_mul, inv_mul_cancel₀ hcard, map_one]
  mul_invOf_self := by
    change algebraMap K (SymmetricRing K (Fin n))
        (Fintype.card H : K) *
      algebraMap K (SymmetricRing K (Fin n))
        (Fintype.card H : K)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hcard, map_one]

section Nonmodular

variable [hcard : Fact ((Fintype.card H : K) ≠ 0)]

local instance nonmodularCardInvertible :
    Invertible (Fintype.card H : SymmetricRing K (Fin n)) :=
  symmetricCardInvertibleOfNeZero K n H hcard.out

theorem invCard_isHomogeneous_zero_of_card_ne_zero_fact :
    IsHomogeneous
      (⅟(Fintype.card H : SymmetricRing K (Fin n))).1 0 := by
  have hinv :
      ⅟(Fintype.card H : SymmetricRing K (Fin n)) =
        algebraMap K (SymmetricRing K (Fin n))
          (Fintype.card H : K)⁻¹ := by
    apply invOf_eq_right_inv
    change algebraMap K (SymmetricRing K (Fin n))
        (Fintype.card H : K) *
      algebraMap K (SymmetricRing K (Fin n))
        (Fintype.card H : K)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hcard.out, map_one]
  rw [hinv]
  exact MvPolynomial.isHomogeneous_C _ _

theorem reynolds_preserves_homogeneous_of_card_ne_zero_fact
    {p : PolynomialRing K (Fin n)} {d : ℕ} (hp : IsHomogeneous p d) :
    IsHomogeneous ((subgroupRepresentation K (Fin n) H).averageMap p) d :=
  LazardInvariantGradedReynolds.reynolds_preserves_homogeneous K (Fin n) H
    (invCard_isHomogeneous_zero_of_card_ne_zero_fact K n H) hp

def reynoldsArtinFixedBasis_of_card_ne_zero_fact :
    BoundedHomogeneousFixedBasis
      (subgroupRepresentation K (Fin n) H).averageMap
      (LinearMap.id (R := SymmetricRing K (Fin n))
        (M := PolynomialRing K (Fin n)))
      (lazardDegreeBound n) :=
  boundedHomogeneousFixedBasis_of_degreeTriangular
    (symmetricArtinBasis K n)
    (LinearMap.id (R := SymmetricRing K (Fin n))
      (M := PolynomialRing K (Fin n)))
    Function.injective_id
    artinDegree (lazardDegreeBound n)
    (by
      intro i
      change IsHomogeneous (symmetricArtinBasis K n i) (artinDegree i)
      exact symmetricArtinBasis_isHomogeneous K n i)
    (symmetricArtinBasis_degree_le n)
    (subgroupRepresentation K (Fin n) H).averageMap
    (LazardInvariantGradedReynolds.reynolds_isIdempotentElem K (Fin n) H)
    (by
      intro p d hp
      change IsHomogeneous p d at hp
      change IsHomogeneous
        ((subgroupRepresentation K (Fin n) H).averageMap p) d
      exact reynolds_preserves_homogeneous_of_card_ne_zero_fact K n H hp)
    (by
      intro i j hij
      exact matrixEntry_eq_zero_of_degree_lt
        (symmetricArtinBasis K n) artinDegree
        (symmetricArtinBasis_isHomogeneous K n)
        (subgroupRepresentation K (Fin n) H).averageMap
        (fun hp =>
          reynolds_preserves_homogeneous_of_card_ne_zero_fact K n H hp)
        i j hij)
    (by
      intro i j hij
      exact exists_matrixEntry_eq_algebraMap
        (symmetricArtinBasis K n) artinDegree
        (symmetricArtinBasis_isHomogeneous K n)
        (subgroupRepresentation K (Fin n) H).averageMap
        (fun hp =>
          reynolds_preserves_homogeneous_of_card_ne_zero_fact K n H hp)
        i j hij)

def lazardHomogeneousInvariantBasis_of_card_ne_zero_fact :
    HomogeneousInvariantBasis K (Fin n) H (lazardDegreeBound n) := by
  let B := reynoldsArtinFixedBasis_of_card_ne_zero_fact K n H
  exact
    { Index := B.Index
      indexFintype := B.indexFintype
      basis := B.basis.map
        (LinearEquiv.ofEq _ _
          (reynolds_fixedSubmodule K (Fin n) H))
      degree := B.degree
      basis_homogeneous := by
        intro i
        rw [Module.Basis.map_apply]
        rw [LinearEquiv.coe_ofEq_apply]
        exact B.basis_homogeneous i
      degree_le := B.degree_le }

end Nonmodular

/-- Corrected form of Lazard's Theorem 2: the subgroup order is nonzero in
the ground field. -/
theorem lazardTheoremTwo_of_card_ne_zero
    (hcard : (Fintype.card H : K) ≠ 0) :
    Nonempty (HomogeneousInvariantBasis K (Fin n) H
      (lazardDegreeBound n)) := by
  letI : Fact ((Fintype.card H : K) ≠ 0) := ⟨hcard⟩
  exact ⟨lazardHomogeneousInvariantBasis_of_card_ne_zero_fact K n H⟩

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample
