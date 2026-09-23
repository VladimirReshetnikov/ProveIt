import Surreal.Algebra.NonnegativePolynomialNorm
import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.Surcomplex.Modulus

/-!
# Norm-square factorization over the actual surreal field

The actual-surreal instance of `trigonometry:lem:twosquares`, including its
half-degree assertion. The required square roots and algebraic closedness
are proved instances on the native sign field and its surcomplexification.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

/-- Every nonnegative actual surreal polynomial has an exact surcomplex norm factor of half degree. -/
theorem nonnegative_polynomial_factorization (p : Polynomial SignSequence.{u})
    (hp : ∀ x : SignSequence.{u}, 0 ≤ p.eval x) :
    ∃ Q : Polynomial Surcomplex.{u},
      p.map ofReal = Q * Q.map conj.toRingHom ∧
      (∀ x : SignSequence.{u}, p.eval x = modulus (Q.eval (ofReal x)) ^ 2) ∧
      Q.natDegree = p.natDegree / 2 := by
  obtain ⟨Q, hQ, he, hd⟩ := Complexify.nonnegative_polynomial_norm_factorization p hp
  refine ⟨Q, hQ, ?_, hd⟩
  intro x
  rw [modulus_sq]
  exact he x

/-- A degree bound `2N` on the nonnegative input gives degree at most `N` for its factor. -/
theorem nonnegative_polynomial_factorization_degree_le (p : Polynomial SignSequence.{u})
    (hp : ∀ x : SignSequence.{u}, 0 ≤ p.eval x) (N : ℕ) (hd : p.natDegree ≤ 2 * N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      p.map ofReal = Q * Q.map conj.toRingHom ∧
      ∀ x : SignSequence.{u}, p.eval x = modulus (Q.eval (ofReal x)) ^ 2 := by
  obtain ⟨Q, hQ, he, hdeg⟩ := nonnegative_polynomial_factorization p hp
  exact ⟨Q, by omega, hQ, he⟩

/-- Actual-field nonnegativity is exactly the existence of a polynomial conjugate-product factor. -/
theorem nonnegative_iff_polynomial_factorization (p : Polynomial SignSequence.{u}) :
    (∀ x : SignSequence.{u}, 0 ≤ p.eval x) ↔
      ∃ Q : Polynomial Surcomplex.{u}, p.map ofReal = Q * Q.map conj.toRingHom :=
  Complexify.nonnegative_iff_polynomial_norm_factor p

end
end Surreal.Surcomplex
