import Surreal.Surcomplex.FejerRieszBoundary
import Surreal.Surcomplex.TrigonometricPolynomialUniqueness

/-!
# Fejér–Riesz existence over actual surreal angles

The equivalence of nonnegativity and polynomial squared-modulus
factorization in `trigonometry:thm:fejer` and `trigonometry:eq:fejer`.
The factor is valid at every finite angle and on the entire actual unit
circle. The separate normalized zero-free factor and uniqueness clauses
are not asserted here.
-/

universe u
namespace Surreal.Surcomplex.FejerRiesz

open Foundations Polynomial

noncomputable section

/-- Every nonnegative real Fourier polynomial has a degree-bounded factor at all finite angles. -/
theorem exists_factor (p : LaurentPolynomial Surcomplex.{u})
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (hp : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      ∀ θ : SignSequence.FiniteElement.{u},
        trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2) := by
  obtain ⟨q, hq, hid, he⟩ := nonnegative_polynomial_factorization_degree_le (numerator p N)
    (numerator_nonnegative p hp N hN) N (natDegree_numerator_le p N hN)
  refine ⟨CayleySpectral.factor q N, CayleySpectral.natDegree_factor_le q N hq, ?_⟩
  intro θ
  apply QuadraticAlgebra.ext
  · change (trigonometricPolynomial p θ).re =
      modulus ((CayleySpectral.factor q N).eval (finitePhase θ)) ^ 2
    by_cases hθ : finitePhase θ = -1
    · have hu : phaseUnit θ = (-1 : Surcomplex.{u}ˣ) := Units.ext (by simpa using hθ)
      simpa only [trigonometricPolynomial, hu, hθ] using factor_at_neg_one p N hN q hq hid
    · let t := cayleyCoord (finitePhase θ)
      have hc : cayley t = finitePhase θ :=
        cayley_cayleyCoord (finitePhaseHom (Multiplicative.ofAdd θ)) hθ
      have hu : cayleyUnit t = phaseUnit θ := Units.ext hc
      have hd : (1 + t ^ 2) ^ N ≠ 0 := pow_ne_zero _ (ne_of_gt (by positivity))
      apply mul_right_cancel₀ hd
      calc
        _ = (numerator p N).eval t := by
          rw [eval_numerator p N hN t, hu, mul_comm]
          rfl
        _ = modulus (q.eval (ofReal t)) ^ 2 := he t
        _ = _ := by
          simpa only [hc] using (CayleySpectral.modulus_sq_factor_cayley_mul q N hq t).symm
  · exact hreal θ

/-- The existence equivalence in Fejér–Riesz, with actual finite-angle quantification. -/
theorem nonnegative_iff_factor (p : LaurentPolynomial Surcomplex.{u})
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    (∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re) ↔
      ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
        ∀ θ : SignSequence.FiniteElement.{u},
          trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2) := by
  refine ⟨fun hp => exists_factor p hreal hp N hN, ?_⟩
  rintro ⟨Q, _, hQ⟩ θ
  rw [hQ θ, ofReal_re]
  exact sq_nonneg _

/-- The manuscript's coefficient symmetry supplies real-valuedness in the existence equivalence. -/
theorem nonnegative_iff_factor_of_conjugate_symmetric (p : LaurentPolynomial Surcomplex.{u})
    (hsym : ∀ k : ℤ, p.coeff (-k) = conj (p.coeff k))
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    (∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re) ↔
      ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
        ∀ θ : SignSequence.FiniteElement.{u},
          trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2) :=
  nonnegative_iff_factor p ((trigonometricPolynomial_real_iff p).mpr hsym) N hN

/-- The same polynomial realizes the factorization on every actual unit-circle point. -/
theorem exists_factor_on_circle (p : LaurentPolynomial Surcomplex.{u})
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (hp : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      ∀ z : UnitCircle.{u}, p.smeval (Unitary.toUnits z) = ofReal (modulus (Q.eval z.val) ^ 2) := by
  obtain ⟨Q, hQ, he⟩ := exists_factor p hreal hp N hN
  refine ⟨Q, hQ, ?_⟩
  intro z
  obtain ⟨θ, hθ⟩ := finitePhaseHom_surjective z
  have hu : phaseUnit θ.toAdd = Unitary.toUnits z := congrArg Unitary.toUnits hθ
  have hv : finitePhase θ.toAdd = z.val := congrArg Subtype.val hθ
  simpa only [trigonometricPolynomial, hu, hv] using he θ.toAdd

end
end Surreal.Surcomplex.FejerRiesz
