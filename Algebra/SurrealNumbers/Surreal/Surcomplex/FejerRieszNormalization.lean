import Surreal.Surcomplex.FejerRieszExistence
import Surreal.Surcomplex.PolynomialPositiveNormalization

/-!
# Normalized Fejér–Riesz factors exist

The existence part of the final clause of `trigonometry:thm:fejer`:
for a nonzero nonnegative real Fourier polynomial the factor can be chosen
without zeros in the open actual unit disk and with positive real value
at zero. Uniqueness of the normalized choice remains a separate theorem.
-/

universe u
namespace Surreal.Surcomplex.FejerRiesz

open Foundations Polynomial

noncomputable section

/-- A factor of a nonzero native Fourier polynomial cannot be the zero polynomial. -/
theorem factor_ne_zero (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (Q : Polynomial Surcomplex.{u})
    (hQ : ∀ θ : SignSequence.FiniteElement.{u},
      trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) : Q ≠ 0 := by
  intro he
  obtain ⟨x, hx⟩ := exists_ordinary_angle_trigonometricPolynomial_ne_zero p hp
  apply hx
  simpa only [he, eval_zero, modulus_zero, zero_pow (by decide : 2 ≠ 0), map_zero] using
    hQ (SignSequence.finiteOfReal x)

/-- The factor can be chosen zero-free in the open unit disk and positive real at zero. -/
theorem exists_normalized_factor (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (hn : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      (∀ θ : SignSequence.FiniteElement.{u},
        trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) ∧
      (∀ z : Surcomplex.{u}, modulus z < 1 → Q.eval z ≠ 0) ∧
      ∃ r : SignSequence.{u}, 0 < r ∧ Q.eval 0 = ofReal r := by
  obtain ⟨P, hPdeg, hP⟩ := exists_factor p hreal hn N hN
  obtain ⟨Q, hQdeg, hmod, hzero, hpos⟩ :=
    exists_normalized_outer_polynomial P (factor_ne_zero p hp P hP)
  refine ⟨Q, hQdeg.trans hPdeg, ?_, hzero, hpos⟩
  intro θ
  rw [hP θ, hmod (finitePhase θ) (modulus_finitePhase θ)]

/-- Coefficient conjugate symmetry gives the same normalized existence statement. -/
theorem exists_normalized_factor_of_conjugate_symmetric
    (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (hsym : ∀ k : ℤ, p.coeff (-k) = conj (p.coeff k))
    (hn : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      (∀ θ : SignSequence.FiniteElement.{u},
        trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) ∧
      (∀ z : Surcomplex.{u}, modulus z < 1 → Q.eval z ≠ 0) ∧
      ∃ r : SignSequence.{u}, 0 < r ∧ Q.eval 0 = ofReal r :=
  exists_normalized_factor p hp ((trigonometricPolynomial_real_iff p).mpr hsym) hn N hN

end
end Surreal.Surcomplex.FejerRiesz
