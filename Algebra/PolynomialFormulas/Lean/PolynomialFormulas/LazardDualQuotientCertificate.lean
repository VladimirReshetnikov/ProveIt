import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Dual certificates for independent classes in a linear quotient

This file isolates the small piece of linear algebra used by the modular
counterexample to Lazard's unrestricted invariant-module theorem.  To prove
that a quotient contains `m` independent classes it is enough to exhibit
`m` linear functionals which kill the subspace generators and pair with
`m` test vectors as the identity matrix.

The statement is deliberately independent of any row-reduction algorithm.
-/

namespace LeanProofs.PolynomialFormulas.LazardDualQuotientCertificate

open scoped BigOperators
open Set Submodule

set_option autoImplicit false

variable {K V ι : Type*} {m : ℕ}
variable [Field K] [AddCommGroup V] [Module K V]

/-- An injective linear realization remains injective after quotienting the
source by `S` and the target by the image of `S`.  This transports a finite
coordinate quotient certificate to its literal polynomial realization. -/
theorem quotientMap_injective_of_injective
    {W : Type*} [AddCommGroup W] [Module K W]
    (S : Submodule K V) (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Function.Injective
      (S.mapQ (S.map f) f (Submodule.le_comap_map f S)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ,
    Submodule.comap_map_eq_of_injective hf S,
    Submodule.mkQ_map_self]

/-- A dual annihilator/test-vector certificate produces linearly independent
classes in the quotient by the span of the source vectors. -/
theorem quotient_linearIndependent_of_dual_certificate
    (source : ι → V) (test : Fin m → V) (dual : Fin m → V →ₗ[K] K)
    (hkill : ∀ i s, dual i (source s) = 0)
    (hpair : ∀ i j, dual i (test j) = if i = j then 1 else 0) :
    LinearIndependent K fun j =>
      (span K (Set.range source)).mkQ (test j) := by
  let S : Submodule K V := span K (Set.range source)
  change LinearIndependent K fun j => S.mkQ (test j)
  rw [Fintype.linearIndependent_iff]
  intro coefficients hsum j
  have hmem : (∑ i, coefficients i • test i) ∈ S := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change S.mkQ (∑ i, coefficients i • test i) = 0
    simpa only [map_sum, map_smul] using hsum
  have hspan : S ≤ LinearMap.ker (dual j) := by
    change span K (Set.range source) ≤ LinearMap.ker (dual j)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, rfl⟩
    exact LinearMap.mem_ker.mpr (hkill j s)
  have hzero : dual j (∑ i, coefficients i • test i) = 0 :=
    LinearMap.mem_ker.mp (hspan hmem)
  simpa [map_sum, map_smul, hpair, eq_comm] using hzero

/-- Finite-dimensional numerical consequence of a dual certificate. -/
theorem quotient_finrank_ge_of_dual_certificate
    [Module.Finite K V]
    (source : ι → V) (test : Fin m → V) (dual : Fin m → V →ₗ[K] K)
    (hkill : ∀ i s, dual i (source s) = 0)
    (hpair : ∀ i j, dual i (test j) = if i = j then 1 else 0) :
    m ≤ Module.finrank K (V ⧸ span K (Set.range source)) := by
  have hli := quotient_linearIndependent_of_dual_certificate
    source test dual hkill hpair
  simpa using hli.fintype_card_le_finrank

end LeanProofs.PolynomialFormulas.LazardDualQuotientCertificate
