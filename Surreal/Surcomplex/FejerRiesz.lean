import Surreal.Surcomplex.FejerRieszNormalization
import Surreal.Surcomplex.OuterPolynomialUniqueness

/-!
# The normalized Fejér–Riesz theorem

Completes `trigonometry:thm:fejer`: the squared-modulus factorization
exists exactly for nonnegative real Fourier polynomials, and a nonzero
input has a unique factor without open-disk zeros and with positive real
value at zero. All angles, coefficients and disk points are actual surreal
or surcomplex elements; no ordinary-field restriction is imposed.
-/

universe u
namespace Surreal.Surcomplex.FejerRiesz

open Foundations Polynomial

noncomputable section

/-- The source's normalization: exact factorization, no open-disk zeros, and positive value at zero. -/
def IsNormalizedFactor (p : LaurentPolynomial Surcomplex.{u}) (Q : Polynomial Surcomplex.{u}) : Prop :=
  (∀ θ : SignSequence.FiniteElement.{u},
    trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) ∧
  (∀ z : Surcomplex.{u}, modulus z < 1 → Q.eval z ≠ 0) ∧
  ∃ r : SignSequence.{u}, 0 < r ∧ Q.eval 0 = ofReal r

/-- Any two normalized factors of the same native Fourier polynomial are equal. -/
theorem normalized_factor_unique (p : LaurentPolynomial Surcomplex.{u})
    (P Q : Polynomial Surcomplex.{u}) (hP : IsNormalizedFactor p P)
    (hQ : IsNormalizedFactor p Q) : P = Q := by
  apply eq_of_normalized_outer_modulus_eq P Q hP.2.1 hQ.2.1 _ hP.2.2 hQ.2.2
  intro z hz
  obtain ⟨θ, hθ⟩ := exists_finitePhase_eq_of_modulus_eq_one z hz
  have he := (hP.1 θ).symm.trans (hQ.1 θ)
  have hs := ofReal_injective he
  rw [hθ] at hs
  nlinarith [modulus_nonneg (P.eval z), modulus_nonneg (Q.eval z)]

/-- Every nonzero nonnegative real Fourier polynomial has a unique normalized factor. -/
theorem existsUnique_normalized_factor (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (hn : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃! Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧ IsNormalizedFactor p Q := by
  obtain ⟨Q, hdeg, hQ⟩ := exists_normalized_factor p hp hreal hn N hN
  refine ⟨Q, ⟨hdeg, hQ⟩, ?_⟩
  intro P hP
  exact normalized_factor_unique p P Q hP.2 hQ

/-- The full source theorem with conjugate-symmetric Fourier coefficients. -/
theorem fejer_riesz (p : LaurentPolynomial Surcomplex.{u})
    (hsym : ∀ k : ℤ, p.coeff (-k) = conj (p.coeff k))
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ((∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re) ↔
      ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
        ∀ θ : SignSequence.FiniteElement.{u},
          trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) ∧
    (p ≠ 0 → (∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re) →
      ∃! Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧ IsNormalizedFactor p Q) := by
  refine ⟨nonnegative_iff_factor_of_conjugate_symmetric p hsym N hN, ?_⟩
  intro hp hn
  exact existsUnique_normalized_factor p hp ((trigonometricPolynomial_real_iff p).mpr hsym) hn N hN

end
end Surreal.Surcomplex.FejerRiesz
