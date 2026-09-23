import Surreal.Algebra.FiniteAutocorrelation
import Surreal.Surcomplex.FejerRieszCoefficients

/-!
# Fourier coefficient bounds from positivity

Completes `trigonometry:cor:coeffbounds` using the actual Fejér–Riesz
factorization and finite autocorrelation inequalities. All coefficients and
bounds are valued in the actual surcomplex and surreal fields.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Polynomial Finset

noncomputable section

/-- The surreal-valued triangle inequality for any finite sum of surcomplex numbers. -/
theorem modulus_sum_le {ι : Type*} (s : Finset ι) (f : ι → Surcomplex.{u}) :
    modulus (∑ j ∈ s, f j) ≤ ∑ j ∈ s, modulus (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [sum_insert hj, sum_insert hj]
    exact (modulus_add_le _ _).trans (add_le_add le_rfl ih)

namespace FejerRiesz

section Factor

variable (p : LaurentPolynomial Surcomplex.{u}) (Q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (hQ : Q.natDegree ≤ N)
    (he : ∀ θ : SignSequence.FiniteElement.{u},
      trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2))

include hN hQ he

/-- Every nonnegative-frequency coefficient is bounded by the constant coefficient. -/
theorem modulus_coeff_nat_le (k : ℕ) (hk : k ≤ N) :
    modulus (p.coeff k) ≤ (p.coeff 0).re := by
  rw [coeff_eq_sum p Q N hN hQ he k hk, coeff_zero_eq_sum_sq p Q N hN hQ he, ofReal_re]
  apply (modulus_sum_le _ _).trans
  simp_rw [modulus_mul, modulus_conj]
  exact FiniteAutocorrelation.autocorrelation_le_sum_sq (fun j => modulus (Q.coeff j)) N k
    (fun j hj => by rw [coeff_eq_zero_of_natDegree_lt (by omega), modulus_zero])

/-- Conjugate symmetry gives the same bound at every positive or negative frequency. -/
theorem modulus_coeff_le (hsym : ∀ k : ℤ, p.coeff (-k) = conj (p.coeff k))
    (k : ℤ) (hk : k.natAbs ≤ N) : modulus (p.coeff k) ≤ (p.coeff 0).re := by
  obtain ⟨m, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact modulus_coeff_nat_le p Q N hN hQ he m (by simpa using hk)
  · rw [hsym, modulus_conj]
    exact modulus_coeff_nat_le p Q N hN hQ he m (by simpa using hk)

/-- At the highest positive frequency the coefficient satisfies the sharper factor-two bound. -/
theorem two_mul_modulus_coeff_top_le (hpos : 0 < N) :
    2 * modulus (p.coeff N) ≤ (p.coeff 0).re := by
  rw [coeff_top_eq_mul p Q N hN hQ he, modulus_mul, modulus_conj,
    coeff_zero_eq_sum_sq p Q N hN hQ he, ofReal_re]
  exact FiniteAutocorrelation.two_mul_endpoints_le_sum_sq (fun j => modulus (Q.coeff j)) N hpos

end Factor

/-- All conclusions of the source coefficient-bound corollary, with an actual polynomial factor. -/
theorem coefficient_bounds (p : LaurentPolynomial Surcomplex.{u})
    (hsym : ∀ k : ℤ, p.coeff (-k) = conj (p.coeff k))
    (hn : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      (∀ θ : SignSequence.FiniteElement.{u},
        trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) ∧
      p.coeff 0 = ofReal (∑ j ∈ range (N + 1), modulus (Q.coeff j) ^ 2) ∧
      (∀ k : ℤ, k.natAbs ≤ N → modulus (p.coeff k) ≤ (p.coeff 0).re) ∧
      (p ≠ 0 → 0 < (p.coeff 0).re) ∧
      (0 < N → 2 * modulus (p.coeff N) ≤ (p.coeff 0).re) := by
  obtain ⟨Q, hQ, he⟩ := exists_factor p ((trigonometricPolynomial_real_iff p).mpr hsym) hn N hN
  exact ⟨Q, hQ, he, coeff_zero_eq_sum_sq p Q N hN hQ he,
    modulus_coeff_le p Q N hN hQ he hsym,
    fun hp => coeff_zero_pos p hp Q N hN hQ he,
    two_mul_modulus_coeff_top_le p Q N hN hQ he⟩

end FejerRiesz
end
end Surreal.Surcomplex
