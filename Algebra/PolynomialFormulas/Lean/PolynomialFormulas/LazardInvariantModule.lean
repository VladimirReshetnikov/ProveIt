import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Module.Projective

/-!
# The invariant-module framework used by Lazard's Theorem 2

This file isolates the non-computational part of the invariant-ring theorem.
Permutations act linearly on the polynomial ring over the full symmetric
subalgebra, and averaging over a subgroup is an honest projection onto its
invariants whenever the subgroup order is invertible.  The latter hypothesis
is the precise condition used by Lazard's orbit-averaging proof.

The remaining part of Theorem 2 is the bounded homogeneous basis construction;
it is deliberately not hidden in this framework.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModule

open MvPolynomial

set_option autoImplicit false

noncomputable section

variable (k σ : Type*) [CommRing k]

/-- The subalgebra of polynomials fixed by a subgroup of the permutation
group of the variables. -/
def invariantSubalgebra (H : Subgroup (Equiv.Perm σ)) :
    Subalgebra k (MvPolynomial σ k) where
  carrier := {p | ∀ h : H, rename h.1 p = p}
  algebraMap_mem' r h := by simp
  add_mem' hp hq h := by rw [map_add, hp h, hq h]
  mul_mem' hp hq h := by rw [map_mul, hp h, hq h]

@[simp]
theorem mem_invariantSubalgebra (H : Subgroup (Equiv.Perm σ))
    (p : MvPolynomial σ k) :
    p ∈ invariantSubalgebra k σ H ↔ ∀ h : H, rename h.1 p = p :=
  Iff.rfl

theorem symmetricSubalgebra_le_invariantSubalgebra
    (H : Subgroup (Equiv.Perm σ)) :
    symmetricSubalgebra σ k ≤ invariantSubalgebra k σ H := by
  intro p hp h
  exact hp h.1

/-- The canonical inclusion from fully symmetric polynomials to the
`H`-invariant subalgebra. -/
def symmetricToInvariant (H : Subgroup (Equiv.Perm σ)) :
    symmetricSubalgebra σ k →ₐ[k] invariantSubalgebra k σ H :=
  Subalgebra.inclusion (symmetricSubalgebra_le_invariantSubalgebra k σ H)

theorem invariantSubalgebra_top :
    invariantSubalgebra k σ ⊤ = symmetricSubalgebra σ k := by
  ext p
  constructor
  · intro hp e
    exact hp ⟨e, trivial⟩
  · intro hp e
    exact hp e.1

section Representation

abbrev SymmetricRing := symmetricSubalgebra σ k
abbrev PolynomialRing := MvPolynomial σ k

/-- Renaming by `h` is linear over the full symmetric subalgebra: symmetric
scalars are fixed by every variable permutation. -/
def renameLinear (h : Equiv.Perm σ) :
    PolynomialRing k σ →ₗ[SymmetricRing k σ] PolynomialRing k σ where
  toFun := rename h
  map_add' p q := map_add (rename h) p q
  map_smul' s p := by
    change rename h (s.1 * p) = s.1 * rename h p
    rw [map_mul, s.2 h]

@[simp]
theorem renameLinear_apply (h : Equiv.Perm σ) (p : PolynomialRing k σ) :
    renameLinear k σ h p = rename h p :=
  rfl

/-- The permutation representation of a subgroup on the polynomial ring,
with the scalar ring restricted to fully symmetric polynomials. -/
def subgroupRepresentation (H : Subgroup (Equiv.Perm σ)) :
    Representation (SymmetricRing k σ) H (PolynomialRing k σ) where
  toFun h := renameLinear k σ h.1
  map_one' := by
    ext p
    simp [renameLinear]
  map_mul' h g := by
    ext p
    simp [renameLinear, rename_rename]

@[simp]
theorem subgroupRepresentation_apply
    (H : Subgroup (Equiv.Perm σ)) (h : H) (p : PolynomialRing k σ) :
    subgroupRepresentation k σ H h p = rename h.1 p :=
  rfl

theorem mem_subgroupRepresentation_invariants
    (H : Subgroup (Equiv.Perm σ)) (p : PolynomialRing k σ) :
    p ∈ (subgroupRepresentation k σ H).invariants ↔
      p ∈ invariantSubalgebra k σ H :=
  Iff.rfl

section Average

variable (H : Subgroup (Equiv.Perm σ)) [Fintype H]
variable [Invertible (Fintype.card H : SymmetricRing k σ)]

/-- Reynolds averaging is a projection onto the subgroup invariants.  This is
the exact averaging step in Lazard's proof, now with its required invertibility
hypothesis explicit. -/
theorem reynolds_isProjection :
    LinearMap.IsProj (subgroupRepresentation k σ H).invariants
      (subgroupRepresentation k σ H).averageMap :=
  (subgroupRepresentation k σ H).isProj_averageMap

theorem reynolds_mem_invariants (p : PolynomialRing k σ) :
    (subgroupRepresentation k σ H).averageMap p ∈
      (subgroupRepresentation k σ H).invariants :=
  (subgroupRepresentation k σ H).averageMap_invariant p

theorem reynolds_eq_self_of_invariant
    (p : PolynomialRing k σ) (hp : p ∈ invariantSubalgebra k σ H) :
    (subgroupRepresentation k σ H).averageMap p = p :=
  (subgroupRepresentation k σ H).averageMap_id p hp

theorem reynolds_range :
    LinearMap.range (subgroupRepresentation k σ H).averageMap =
      (subgroupRepresentation k σ H).invariants :=
  (reynolds_isProjection k σ H).range

theorem reynolds_invariants_isCompl_kernel :
    IsCompl (subgroupRepresentation k σ H).invariants
      (LinearMap.ker (subgroupRepresentation k σ H).averageMap) :=
  (reynolds_isProjection k σ H).isCompl

/-- Once the ambient polynomial ring is known to be projective over the
symmetric ring (in particular, once the Artin basis is constructed), Reynolds
averaging makes every subgroup-invariant module projective by an explicit
split inclusion. -/
theorem invariantModule_projective
    [Module.Projective (SymmetricRing k σ) (PolynomialRing k σ)] :
    Module.Projective (SymmetricRing k σ)
      (subgroupRepresentation k σ H).invariants := by
  let h := reynolds_isProjection k σ H
  exact Module.Projective.of_split
    (Submodule.subtype (subgroupRepresentation k σ H).invariants)
    h.codRestrict (by
      apply LinearMap.ext
      intro p
      exact h.codRestrict_apply_cod p)

end Average

end Representation

end

end LeanProofs.PolynomialFormulas.LazardInvariantModule
