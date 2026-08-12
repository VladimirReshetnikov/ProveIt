import PolynomialFormulas.LazardInvariantModule
import PolynomialFormulas.LazardInvariantProjectionBlocks
import PolynomialFormulas.LazardInvariantArtinModuleBasis
import PolynomialFormulas.LazardInvariantFiniteDegreeInduction
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The graded Reynolds target

This file assembles the finite block induction into a basis of the subgroup
invariants over the full symmetric ring, consisting of homogeneous
polynomials whose degrees are bounded by the largest degree in the ambient
Artin basis.

The general Reynolds lemmas keep the averaging hypothesis explicit: the
subgroup is finite and its cardinality is invertible in the symmetric
coefficient ring.  The final characteristic-zero theorem constructs that
inverse internally.  Reynolds averaging is then an idempotent endomorphism
whose fixed module is the invariant module.
`LazardInvariantFiniteDegreeInduction` iterates the two-block step and descends
each constant diagonal block to finite-dimensional linear algebra over the
ground field.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantGradedReynolds

open MvPolynomial

set_option autoImplicit false

noncomputable section

open LazardInvariantModule
open LazardInvariantProjectionBlocks
open LazardInvariantArtinBasis
open LazardInvariantArtinModuleBasis
open LazardInvariantHomogeneousCoordinates
open LazardInvariantFiniteDegreeInduction

variable (k σ : Type*) [CommRing k]

/-- The degree bound occurring in Lazard's theorem for `n` variables. -/
def lazardDegreeBound (n : ℕ) : ℕ := n * (n - 1) / 2

/-- A finite homogeneous ambient basis with a visible uniform degree bound. -/
structure HomogeneousAmbientBasis
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (degreeBound : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  basis : Module.Basis Index A M
  degree : Index → ℕ
  homogeneous : Index → Prop
  basis_homogeneous (i : Index) : homogeneous i
  degree_le (i : Index) : degree i ≤ degreeBound

/-- The ambient Artin construction supplies the bounded homogeneous basis
needed by the Reynolds block induction. -/
def artinAmbientBasis [IsDomain k] (n : ℕ) :
    HomogeneousAmbientBasis
      (MvPolynomial.symmetricSubalgebra (Fin n) k)
      (MvPolynomial (Fin n) k) (lazardDegreeBound n) where
  Index := ArtinIndex n
  indexFintype := inferInstance
  basis := symmetricArtinBasis k n
  degree := artinDegree
  homogeneous a :=
    IsHomogeneous (symmetricArtinBasis k n a) (artinDegree a)
  basis_homogeneous := symmetricArtinBasis_isHomogeneous k n
  degree_le := symmetricArtinBasis_degree_le n

/-- The precise bounded homogeneous-basis conclusion of Lazard's Theorem 2
for a particular subgroup. -/
structure HomogeneousInvariantBasis
    (H : Subgroup (Equiv.Perm σ)) (degreeBound : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  basis : Module.Basis Index (SymmetricRing k σ)
    (subgroupRepresentation k σ H).invariants
  degree : Index → ℕ
  basis_homogeneous (i : Index) :
    IsHomogeneous (basis i).1 (degree i)
  degree_le (i : Index) : degree i ≤ degreeBound

/-- The exact certificate produced by the graded block argument.  It is
deliberately stated for the range of an endomorphism, rather than for subgroup
invariants: the block construction first builds a basis for the Reynolds
range, and Reynolds' theorem subsequently identifies that range with the
invariant module.  The conditional transport theorem below is useful on its
own; `reynoldsArtinFixedBasis` later constructs the corresponding certificate
unconditionally in the characteristic-zero setting. -/
structure BoundedHomogeneousRangeBasis
    (p : PolynomialRing k σ →ₗ[SymmetricRing k σ] PolynomialRing k σ)
    (degreeBound : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  basis : Module.Basis Index (SymmetricRing k σ) (LinearMap.range p)
  degree : Index → ℕ
  basis_homogeneous (i : Index) :
    IsHomogeneous (basis i).1 (degree i)
  degree_le (i : Index) : degree i ≤ degreeBound

section Average

variable (H : Subgroup (Equiv.Perm σ)) [Fintype H]
variable [Invertible (Fintype.card H : SymmetricRing k σ)]

/-- Reynolds averaging is honestly idempotent under the visible group-order
invertibility hypothesis. -/
theorem reynolds_isIdempotentElem :
    IsIdempotentElem (subgroupRepresentation k σ H).averageMap :=
  (reynolds_isProjection k σ H).isIdempotentElem

/-- The explicit finite-sum formula for Reynolds averaging. -/
theorem reynolds_averageMap_apply (p : PolynomialRing k σ) :
    (subgroupRepresentation k σ H).averageMap p =
      (⅟(Fintype.card H : SymmetricRing k σ)) •
        ∑ h : H, MvPolynomial.rename h.1 p := by
  simp [Representation.averageMap, GroupAlgebra.average,
    map_smul, map_sum, Representation.asAlgebraHom_of,
    subgroupRepresentation_apply]

/-- Reynolds averaging preserves ordinary polynomial degree once the visible
averaging scalar is known to be homogeneous of degree zero.  Over `ℚ` this
scalar is the constant polynomial `1 / |H|`. -/
theorem reynolds_preserves_homogeneous
    (hinv : IsHomogeneous
      (⅟(Fintype.card H : SymmetricRing k σ)).1 0)
    {p : PolynomialRing k σ} {d : ℕ} (hp : IsHomogeneous p d) :
    IsHomogeneous ((subgroupRepresentation k σ H).averageMap p) d := by
  rw [reynolds_averageMap_apply]
  change IsHomogeneous
    ((⅟(Fintype.card H : SymmetricRing k σ)).1 *
      ∑ h : H, MvPolynomial.rename h.1 p) d
  have hsum : IsHomogeneous
      (∑ h : H, MvPolynomial.rename h.1 p) d := by
    apply MvPolynomial.IsHomogeneous.sum Finset.univ _ d
    intro h _
    exact hp.rename_isHomogeneous
  simpa using hinv.mul hsum

/-- The fixed module of Reynolds averaging is exactly the subgroup-invariant
module. -/
theorem reynolds_fixedSubmodule :
    (subgroupRepresentation k σ H).averageMap.fixedSubmodule =
      (subgroupRepresentation k σ H).invariants := by
  calc
    _ = LinearMap.range (subgroupRepresentation k σ H).averageMap :=
      (range_eq_fixedSubmodule _ (reynolds_isIdempotentElem k σ H)).symm
    _ = _ := reynolds_range k σ H

/-- Transport the bounded homogeneous range basis produced by the graded
upper-triangular induction across the honest Reynolds range theorem.  This
proves every part of the basis conclusion once the explicit certificate `B`
has been constructed; it does not manufacture that certificate. -/
def homogeneousInvariantBasisOfReynoldsRange
    (degreeBound : ℕ)
    (B : BoundedHomogeneousRangeBasis k σ
      (subgroupRepresentation k σ H).averageMap degreeBound) :
    HomogeneousInvariantBasis k σ H degreeBound where
  Index := B.Index
  indexFintype := B.indexFintype
  basis := B.basis.map
    (LinearEquiv.ofEq _ _ (reynolds_range k σ H))
  degree := B.degree
  basis_homogeneous i := by
    rw [Module.Basis.map_apply]
    rw [LinearEquiv.coe_ofEq_apply]
    exact B.basis_homogeneous i
  degree_le := B.degree_le

/-- A public, hypothesis-explicit form of Lazard's Theorem 2 conclusion.

The conclusion says that the invariant module is free on a finite homogeneous
basis of degrees at most `n(n-1)/2`.  The extra argument exposes the output of
the graded Reynolds block induction as a reusable interface.  In characteristic
zero the remaining typeclass hypothesis merely records that division by `|H|`
used by Reynolds averaging is available in the symmetric coefficient ring. -/
theorem lazardTheoremTwo_of_gradedBlockInduction [Fintype σ]
    (B : BoundedHomogeneousRangeBasis k σ
      (subgroupRepresentation k σ H).averageMap
      (lazardDegreeBound (Fintype.card σ))) :
    Nonempty (HomogeneousInvariantBasis k σ H
      (lazardDegreeBound (Fintype.card σ))) :=
  ⟨homogeneousInvariantBasisOfReynoldsRange k σ H
    (lazardDegreeBound (Fintype.card σ)) B⟩

end Average

section FieldAverage

variable (K τ : Type*) [Field K] [CharZero K]

/-- A nonzero natural-number constant is a unit in the symmetric polynomial
subalgebra over a characteristic-zero field.  This supplies the averaging
inverse internally rather than leaving it as an extra theorem hypothesis. -/
def symmetricNatCastInvertible (m : ℕ) (hm : m ≠ 0) :
    Invertible (m : SymmetricRing K τ) where
  invOf := algebraMap K (SymmetricRing K τ) (m : K)⁻¹
  invOf_mul_self := by
    have hmK : (m : K) ≠ 0 := by exact_mod_cast hm
    change
      algebraMap K (SymmetricRing K τ) (m : K)⁻¹ *
          algebraMap K (SymmetricRing K τ) (m : K) = 1
    rw [← map_mul, inv_mul_cancel₀ hmK, map_one]
  mul_invOf_self := by
    have hmK : (m : K) ≠ 0 := by exact_mod_cast hm
    change
      algebraMap K (SymmetricRing K τ) (m : K) *
          algebraMap K (SymmetricRing K τ) (m : K)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hmK, map_one]

variable (H : Subgroup (Equiv.Perm τ)) [Fintype H]

local instance fieldAverageCardInvertible :
    Invertible (Fintype.card H : SymmetricRing K τ) :=
  symmetricNatCastInvertible K τ (Fintype.card H) Fintype.card_ne_zero

/-- Over a characteristic-zero field, the averaging scalar is the constant
polynomial `1 / |H|`, hence homogeneous of degree zero. -/
theorem invCard_isHomogeneous_zero :
    IsHomogeneous
      (⅟(Fintype.card H : SymmetricRing K τ)).1 0 := by
  have hcard : (Fintype.card H : K) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hinv :
      ⅟(Fintype.card H : SymmetricRing K τ) =
        algebraMap K (SymmetricRing K τ) ((Fintype.card H : K)⁻¹) := by
    apply invOf_eq_right_inv
    change
      algebraMap K (SymmetricRing K τ) (Fintype.card H : K) *
        algebraMap K (SymmetricRing K τ) ((Fintype.card H : K)⁻¹) = 1
    rw [← map_mul]
    simp [hcard]
  rw [hinv]
  exact MvPolynomial.isHomogeneous_C _ _

/-- Therefore Reynolds averaging itself preserves homogeneity over every
characteristic-zero field. -/
theorem reynolds_preserves_homogeneous_charZero
    {p : PolynomialRing K τ} {d : ℕ} (hp : IsHomogeneous p d) :
    IsHomogeneous ((subgroupRepresentation K τ H).averageMap p) d :=
  reynolds_preserves_homogeneous K τ H
    (invCard_isHomogeneous_zero K τ H) hp

end FieldAverage

section LazardTheoremTwo

variable (K : Type*) [Field K] [CharZero K]
variable (n : ℕ)
variable (H : Subgroup (Equiv.Perm (Fin n))) [Fintype H]

local instance lazardCardInvertible :
    Invertible (Fintype.card H : SymmetricRing K (Fin n)) :=
  symmetricNatCastInvertible K (Fin n) (Fintype.card H)
    Fintype.card_ne_zero

/-- The finite-degree induction applied to the homogeneous Artin basis and
the Reynolds projection.  Unlike
`lazardTheoremTwo_of_gradedBlockInduction`, this definition constructs the
graded fixed-basis certificate rather than taking it as an argument. -/
def reynoldsArtinFixedBasis :
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
    (reynolds_isIdempotentElem K (Fin n) H)
    (by
      intro p d hp
      change IsHomogeneous p d at hp
      change IsHomogeneous
        ((subgroupRepresentation K (Fin n) H).averageMap p) d
      exact reynolds_preserves_homogeneous_charZero K (Fin n) H hp)
    (by
      intro i j hij
      exact matrixEntry_eq_zero_of_degree_lt
        (symmetricArtinBasis K n) artinDegree
        (symmetricArtinBasis_isHomogeneous K n)
        (subgroupRepresentation K (Fin n) H).averageMap
        (fun hp => reynolds_preserves_homogeneous_charZero K (Fin n) H hp)
        i j hij)
    (by
      intro i j hij
      exact exists_matrixEntry_eq_algebraMap
        (symmetricArtinBasis K n) artinDegree
        (symmetricArtinBasis_isHomogeneous K n)
        (subgroupRepresentation K (Fin n) H).averageMap
        (fun hp => reynolds_preserves_homogeneous_charZero K (Fin n) H hp)
        i j hij)

/-- The constructed homogeneous fixed basis, transported across the theorem
identifying Reynolds-fixed vectors with subgroup invariants. -/
def lazardHomogeneousInvariantBasis :
    HomogeneousInvariantBasis K (Fin n) H (lazardDegreeBound n) := by
  let B := reynoldsArtinFixedBasis K n H
  exact
    { Index := B.Index
      indexFintype := B.indexFintype
      basis := B.basis.map
        (LinearEquiv.ofEq _ _ (reynolds_fixedSubmodule K (Fin n) H))
      degree := B.degree
      basis_homogeneous := by
        intro i
        rw [Module.Basis.map_apply]
        rw [LinearEquiv.coe_ofEq_apply]
        exact B.basis_homogeneous i
      degree_le := B.degree_le }

/-- Lazard's Theorem 2 for `n` variables over a characteristic-zero field:
the invariants of every finite permutation subgroup form a finite free module
over the full symmetric ring, with a homogeneous basis of degrees at most
`n(n-1)/2`.

The inverse of `|H|` in the symmetric ring is constructed internally from
characteristic zero; there is no additional averaging certificate in the
statement. -/
theorem lazardTheoremTwo :
    Nonempty (HomogeneousInvariantBasis K (Fin n) H
      (lazardDegreeBound n)) :=
  ⟨lazardHomogeneousInvariantBasis K n H⟩

end LazardTheoremTwo

end

end LeanProofs.PolynomialFormulas.LazardInvariantGradedReynolds
