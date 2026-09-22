import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# The invertible linearization of a coprime polynomial product

The linearization `polynomial:eq:factorlinear`, preceding `polynomial:thm:hensel` in
`docs/surcomplex/polynomial-algebra/article.tex` is
`(h, k) ↦ h * q + p * k` in the binary case. Its source consists of
perturbations of degrees below those of the corresponding factors; its
target consists of polynomials of degree below the sum of the factor degrees.

Mathlib's Sylvester map is exactly this map, up to commutativity of the
displayed products. Its determinant is the resultant, which is a unit
when the factors are coprime and the first is monic. Consequently the
linearization is an isomorphism over any commutative coefficient ring,
including rings with zero divisors and factors of degree zero. Monicity
of the second factor is not needed for this finite algebraic assertion.

This is the finite algebra prerequisite for support-controlled Hensel
lifting, not the infinite lifting or a surreal real-closedness theorem.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- The derivative of binary polynomial multiplication on perturbations
that preserve each factor's leading coefficient and degree bound. -/
def factorLinearMap (p q : R[X]) :
    degreeLT R p.natDegree × degreeLT R q.natDegree →ₗ[R]
      degreeLT R (p.natDegree + q.natDegree) :=
  sylvesterMap p q le_rfl le_rfl

/-- The native Sylvester-map convention gives precisely the product
linearization, with the first perturbation attached to the first factor. -/
@[simp] theorem factorLinearMap_apply (p q : R[X])
    (h : degreeLT R p.natDegree) (k : degreeLT R q.natDegree) :
    (factorLinearMap p q (h, k) : R[X]) = (h : R[X]) * q + p * (k : R[X]) := by
  change p * (k : R[X]) + q * (h : R[X]) = _
  ring

/-- Coprime monic factors have an invertible bounded-degree product
linearization. The first factor being monic already suffices. -/
def factorLinearEquiv (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q) :
    (degreeLT R p.natDegree × degreeLT R q.natDegree) ≃ₗ[R]
      degreeLT R (p.natDegree + q.natDegree) :=
  LinearEquiv.ofIsUnitDet
    (f := factorLinearMap p q)
    (v := ((degreeLT.basis R p.natDegree).prod
      (degreeLT.basis R q.natDegree)).reindex finSumFinEquiv)
    (v' := degreeLT.basis R (p.natDegree + q.natDegree)) (by
      rw [factorLinearMap, toMatrix_sylvesterMap']
      exact (isUnit_resultant_iff_isCoprime hp).mpr hpq)

@[simp] theorem factorLinearEquiv_toLinearMap (p q : R[X])
    (hp : p.Monic) (hpq : IsCoprime p q) :
    (factorLinearEquiv p q hp hpq :
      degreeLT R p.natDegree × degreeLT R q.natDegree →ₗ[R]
        degreeLT R (p.natDegree + q.natDegree)) = factorLinearMap p q := rfl

/-- The forward equivalence retains the explicit multiplication formula. -/
@[simp] theorem factorLinearEquiv_apply (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (h : degreeLT R p.natDegree) (k : degreeLT R q.natDegree) :
    (factorLinearEquiv p q hp hpq (h, k) : R[X]) =
      (h : R[X]) * q + p * (k : R[X]) :=
  factorLinearMap_apply p q h k

/-- The inverse returns the unique bounded corrections to a prescribed
coefficient of the product. -/
def factorCorrection (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q) :
    degreeLT R (p.natDegree + q.natDegree) →ₗ[R]
      degreeLT R p.natDegree × degreeLT R q.natDegree :=
  (factorLinearEquiv p q hp hpq).symm.toLinearMap

/-- Correcting by the inverse linearization gives exactly the desired
polynomial, not only its class modulo the product. -/
theorem factorCorrection_spec (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (f : degreeLT R (p.natDegree + q.natDegree)) :
    ((factorCorrection p q hp hpq f).1 : R[X]) * q +
      p * ((factorCorrection p q hp hpq f).2 : R[X]) = f := by
  have h := congrArg (fun a : degreeLT R (p.natDegree + q.natDegree) => (a : R[X]))
    ((factorLinearEquiv p q hp hpq).apply_symm_apply f)
  rw [← factorLinearEquiv_apply]
  exact h

/-- The linearized correction is unique with the prescribed degree bounds. -/
theorem factorCorrection_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (f : degreeLT R (p.natDegree + q.natDegree))
    (h : degreeLT R p.natDegree) (k : degreeLT R q.natDegree)
    (heq : (h : R[X]) * q + p * (k : R[X]) = f) :
    (h, k) = factorCorrection p q hp hpq f := by
  apply (factorLinearEquiv p q hp hpq).injective
  apply Subtype.ext
  simpa only [factorCorrection, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    factorLinearEquiv_apply] using heq

/-- Unbundled existence and uniqueness, with polynomial degree bounds
that also correctly force zero perturbations when a factor has degree zero. -/
theorem existsUnique_bounded_factor_correction (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (f : R[X])
    (hf : f.degree < (p.natDegree + q.natDegree : ℕ)) :
    ∃! hk : R[X] × R[X], hk.1.degree < p.natDegree ∧
      hk.2.degree < q.natDegree ∧ hk.1 * q + p * hk.2 = f := by
  let f' : degreeLT R (p.natDegree + q.natDegree) := ⟨f, mem_degreeLT.mpr hf⟩
  let hk := factorCorrection p q hp hpq f'
  refine ⟨(hk.1, hk.2), ⟨mem_degreeLT.mp hk.1.property,
    mem_degreeLT.mp hk.2.property, factorCorrection_spec p q hp hpq f'⟩, ?_⟩
  rintro ⟨h, k⟩ ⟨hh, hk', heq⟩
  have he := factorCorrection_unique p q hp hpq f'
    ⟨h, mem_degreeLT.mpr hh⟩ ⟨k, mem_degreeLT.mpr hk'⟩ heq
  exact congrArg (fun a : degreeLT R p.natDegree × degreeLT R q.natDegree =>
    ((a.1 : R[X]), (a.2 : R[X]))) he

/-- The exact quadratic remainder after linearization of multiplication.
The residual product of corrections is the higher-order term used in a
support recursion for Hensel lifting. -/
theorem mul_perturbation_eq_linearization (p q : R[X])
    (h : degreeLT R p.natDegree) (k : degreeLT R q.natDegree) :
    (p + (h : R[X])) * (q + (k : R[X])) = p * q +
      (factorLinearMap p q (h, k) : R[X]) + (h : R[X]) * (k : R[X]) := by
  rw [factorLinearMap_apply]
  ring

end

end Surreal.FinitePolynomial
