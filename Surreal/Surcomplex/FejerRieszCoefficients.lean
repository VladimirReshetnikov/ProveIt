import Surreal.Surcomplex.FejerRiesz
import Surreal.Surcomplex.TrigonometricPolynomialRootCount

/-!
# Coefficients of Fejér–Riesz factors

The finite coefficient identities and positivity bounds in
`trigonometry:cor:coeffbounds`, on the actual surreal and surcomplex fields.
-/

universe u
namespace Surreal.Surcomplex.FejerRiesz

open Foundations Polynomial Finset

noncomputable section

/-- The norm encoding has the autocorrelation coefficients of the original polynomial. -/
theorem coeff_circleNormPolynomial (Q : Polynomial Surcomplex.{u}) (N k : ℕ)
    (hQ : Q.natDegree ≤ N) :
    (circleNormPolynomial Q N).coeff (N + k) =
      ∑ j ∈ range (N + 1), Q.coeff (j + k) * conj (Q.coeff j) := by
  classical
  have hR : (conjugateReflect Q N).natDegree ≤ N := by
    apply natDegree_reflect_le.trans
    apply max_le le_rfl
    rwa [natDegree_map_eq_of_injective conj.injective]
  rw [circleNormPolynomial, mul_comm, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑ j ∈ range (N + 1),
        (conjugateReflect Q N).coeff j * Q.coeff (N + k - j) := by
      symm
      apply sum_subset (range_mono (by omega))
      intro j _ hj
      rw [coeff_eq_zero_of_natDegree_lt (by simp only [mem_range] at hj; omega), zero_mul]
    _ = ∑ j ∈ range (N + 1),
        (conjugateReflect Q N).coeff (N - j) * Q.coeff (N + k - (N - j)) := by
      simpa only [Nat.add_sub_cancel] using (sum_range_reflect
        (fun j => (conjugateReflect Q N).coeff j * Q.coeff (N + k - j)) (N + 1)).symm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hj' : j ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      rw [conjugateReflect, coeff_reflect, revAt_le (by omega), coeff_map]
      have h₁ : N - (N - j) = j := by omega
      have h₂ : N + k - (N - j) = j + k := by omega
      rw [h₁, h₂]
      exact mul_comm _ _

/-- Factorization on finite angles identifies the cleared Laurent polynomial with its norm encoding. -/
theorem polynomial_eq_circleNormPolynomial (p : LaurentPolynomial Surcomplex.{u})
    (Q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (hQ : Q.natDegree ≤ N)
    (he : ∀ θ : SignSequence.FiniteElement.{u},
      trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) :
    LaurentAlgebraization.polynomial N p.coeff = circleNormPolynomial Q N := by
  apply polynomial_eq_of_unit_circle
  intro z hz
  obtain ⟨θ, rfl⟩ := exists_finitePhase_eq_of_modulus_eq_one z hz
  rw [eval_circleNormPolynomial Q N hQ _ (modulus_finitePhase θ),
    LaurentAlgebraization.eval_polynomial N p.coeff _
      (FiniteFourier.ne_zero_of_modulus_eq_one (modulus_finitePhase θ))]
  change _ * FiniteFourier.laurentEval N p.coeff (finitePhase θ) = _
  rw [← trigonometricPolynomial_eq_laurentSum p N hN θ, he θ]

/-- Each nonnegative Fourier coefficient is a finite autocorrelation of factor coefficients. -/
theorem coeff_eq_sum (p : LaurentPolynomial Surcomplex.{u})
    (Q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (hQ : Q.natDegree ≤ N)
    (he : ∀ θ : SignSequence.FiniteElement.{u},
      trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2))
    (k : ℕ) (hk : k ≤ N) :
    p.coeff k = ∑ j ∈ range (N + 1), Q.coeff (j + k) * conj (Q.coeff j) := by
  have h := congrArg (fun P : Polynomial Surcomplex.{u} => P.coeff (N + k))
    (polynomial_eq_circleNormPolynomial p Q N hN hQ he)
  rw [LaurentAlgebraization.coeff_polynomial, if_pos (by omega),
    coeff_circleNormPolynomial Q N k hQ] at h
  simpa only [Nat.cast_add, add_sub_cancel_left] using h


/-- The constant Fourier coefficient is the sum of squared moduli of factor coefficients. -/
theorem coeff_zero_eq_sum_sq (p : LaurentPolynomial Surcomplex.{u})
    (Q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (hQ : Q.natDegree ≤ N)
    (he : ∀ θ : SignSequence.FiniteElement.{u},
      trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) :
    p.coeff 0 = ofReal (∑ j ∈ range (N + 1), modulus (Q.coeff j) ^ 2) := by
  simpa only [Nat.cast_zero, Nat.add_zero, mul_conj, modulus_sq, map_sum] using
    coeff_eq_sum p Q N hN hQ he 0 (Nat.zero_le N)

/-- The highest Fourier coefficient uses only the two endpoint factor coefficients. -/
theorem coeff_top_eq_mul (p : LaurentPolynomial Surcomplex.{u})
    (Q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (hQ : Q.natDegree ≤ N)
    (he : ∀ θ : SignSequence.FiniteElement.{u},
      trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) :
    p.coeff N = Q.coeff N * conj (Q.coeff 0) := by
  rw [coeff_eq_sum p Q N hN hQ he N le_rfl]
  rw [sum_eq_single_of_mem 0 (mem_range.mpr (by omega)), Nat.zero_add]
  intro j _ hj
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- A nonzero Fourier polynomial with a squared-modulus factor has positive constant coefficient. -/
theorem coeff_zero_pos (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0)
    (Q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (hQ : Q.natDegree ≤ N)
    (he : ∀ θ : SignSequence.FiniteElement.{u},
      trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2)) :
    0 < (p.coeff 0).re := by
  have hne := factor_ne_zero p hp Q he
  have hc : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  rw [coeff_zero_eq_sum_sq p Q N hN hQ he, ofReal_re]
  apply lt_of_lt_of_le (sq_pos_of_pos (modulus_pos hc))
  exact single_le_sum (fun j _ => sq_nonneg (modulus (Q.coeff j)))
    (mem_range.mpr (by omega))

end
end Surreal.Surcomplex.FejerRiesz
