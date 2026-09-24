import Surreal.Algebra.PolynomialFactorUniqueness
import Surreal.Surcomplex.PolynomialReduction

/-!
# Uniqueness of factors over the actual finite surcomplex ring

The standard-part homomorphism reflects units. Coprime monic complex
reductions therefore imply coprimeness of the actual finite polynomials,
and determine any monic binary factorization uniquely. These are uniqueness
and coprimeness clauses of `polynomial:thm:hensel` on the actual carrier;
existence of such lifts remains a separate obligation.
-/

universe u

namespace Surreal.Surcomplex

noncomputable section

open Polynomial

/-- An actual finite surcomplex element is a unit of the finite ring exactly
when its ordinary complex standard part is nonzero. -/
theorem finite_isUnit_iff_standardPart_ne_zero (z : finiteSubring.{u}) :
    IsUnit z ↔ standardPartHom z ≠ 0 := by
  rw [finiteSubring_integers.isUnit_iff_valuation_eq_one]
  change valuation z.1 = 0 ↔ standardPart z.1 ≠ 0
  exact valuation_eq_zero_iff_standardPart_ne_zero z.2

/-- The actual finite-ring standard-part map reflects units. -/
theorem standardPartHom_reflects_units (z : finiteSubring.{u})
    (hz : IsUnit (standardPartHom z)) : IsUnit z :=
  (finite_isUnit_iff_standardPart_ne_zero z).mpr hz.ne_zero

/-- Coprime monic standard parts imply coprimeness already in the actual finite ring. -/
theorem isCoprime_of_monic_standardPart {p q : Polynomial finiteSubring.{u}}
    (hp : p.Monic) (hq : q.Monic)
    (hcop : IsCoprime (p.map standardPartHom) (q.map standardPartHom)) : IsCoprime p q :=
  FinitePolynomial.isCoprime_of_monic_reductions standardPartHom
    standardPartHom_reflects_units hp hq hcop

/-- Any two monic factorizations with the same coprime complex reductions coincide. -/
theorem monic_factorization_unique_of_standardPart
    {p q p' q' : Polynomial finiteSubring.{u}}
    (hp : p.Monic) (hq : q.Monic) (hp' : p'.Monic) (hq' : q'.Monic)
    (hcop : IsCoprime (p.map standardPartHom) (q.map standardPartHom))
    (hredp : p'.map standardPartHom = p.map standardPartHom)
    (hredq : q'.map standardPartHom = q.map standardPartHom)
    (hmul : p * q = p' * q') : p' = p ∧ q' = q :=
  FinitePolynomial.monic_factorization_unique_of_reductions standardPartHom
    standardPartHom_reflects_units hp hq hp' hq' hcop hredp hredq hmul

/-- The same uniqueness holds for every finite family of pairwise coprime reductions. -/
theorem monic_finite_factorization_unique_of_standardPart {ι : Type*} [Fintype ι]
    (p p' : ι → Polynomial finiteSubring.{u})
    (hp : ∀ i, (p i).Monic) (hp' : ∀ i, (p' i).Monic)
    (hcop : Pairwise fun i j => IsCoprime ((p i).map standardPartHom) ((p j).map standardPartHom))
    (hred : ∀ i, (p' i).map standardPartHom = (p i).map standardPartHom)
    (hmul : ∏ i, p i = ∏ i, p' i) : p' = p :=
  FinitePolynomial.monic_finite_factorization_unique_of_reductions standardPartHom
    standardPartHom_reflects_units p p' hp hp' hcop hred hmul

end

end Surreal.Surcomplex
