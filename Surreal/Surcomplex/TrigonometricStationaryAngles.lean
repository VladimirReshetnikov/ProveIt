import Surreal.Surcomplex.TrigonometricFrequencyDerivative
import Surreal.Surcomplex.AngularLaurentEvaluation

/-!
# The sharp finite bound on stationary angles

The second assertion of `trigonometry:cor:chebyshev`: a nonconstant real
trigonometric polynomial of degree at most `N` has at most `2N` stationary
finite-angle classes modulo ordinary full turns. Stationarity uses the
actual native fine derivative. A stronger version counts the derivative's
native angular-series multiplicities.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- At most `2N` distinct phase classes can be stationary for a nonconstant real Fourier polynomial. -/
theorem card_stationary_angles_le (p : LaurentPolynomial Surcomplex.{u})
    (hp : p ≠ LaurentPolynomial.C (p.coeff 0))
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, FineHasDerivAt (trigonometricFunction p) 0 θ.val)
    (hinj : Set.InjOn finitePhase (S : Set SignSequence.FiniteElement.{u})) :
    S.card ≤ 2 * N := by
  have hd : angularDerivative p ≠ 0 := fun h => hp ((angularDerivative_eq_zero_iff p).mp h)
  apply card_trigonometricPolynomial_roots_le (angularDerivative p) hd N
    (angularDerivative_frequency_bound p N hN) S _ hinj
  intro θ hθ
  exact (stationary_iff_angularDerivative_zero p hreal θ).mp (hS θ hθ)

/-- The same bound counts stationary classes with their derivative-germ multiplicities. -/
theorem sum_stationary_orders_le (p : LaurentPolynomial Surcomplex.{u})
    (hp : p ≠ LaurentPolynomial.C (p.coeff 0))
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, FineHasDerivAt (trigonometricFunction p) 0 θ.val)
    (hinj : Set.InjOn finitePhase (S : Set SignSequence.FiniteElement.{u})) :
    ∑ θ ∈ S, (AngularLaurent.germ (angularDerivative p) (phaseUnit θ)).order.toNat ≤ 2 * N := by
  have hd : angularDerivative p ≠ 0 := fun h => hp ((angularDerivative_eq_zero_iff p).mp h)
  apply AngularLaurent.sum_angular_orders_le (angularDerivative p) hd N
    (angularDerivative_frequency_bound p N hN) S _ hinj
  intro θ hθ
  exact (stationary_iff_angularDerivative_zero p hreal θ).mp (hS θ hθ)

/-- The constant-coefficient exclusion follows from nonconstancy of the actual finite-angle function. -/
theorem ne_constant_of_trigonometricFunction_ne
    (p : LaurentPolynomial Surcomplex.{u}) (θ φ : SignSequence.FiniteElement.{u})
    (h : trigonometricFunction p θ.val ≠ trigonometricFunction p φ.val) :
    p ≠ LaurentPolynomial.C (p.coeff 0) := by
  intro he
  apply h
  rw [he]
  simp only [trigonometricFunction_eq, trigonometricPolynomial, LaurentPolynomial.smeval_C]

/-- The stationary-angle bound stated using nonconstancy of function values and ordinary periods. -/
theorem stationary_angles_bound (p : LaurentPolynomial Surcomplex.{u})
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (hnonconstant : ∃ θ φ : SignSequence.FiniteElement.{u},
      trigonometricFunction p θ.val ≠ trigonometricFunction p φ.val)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, FineHasDerivAt (trigonometricFunction p) 0 θ.val)
    (hperiod : ∀ θ ∈ S, ∀ φ ∈ S, ∀ n : ℤ,
      θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) → θ = φ) :
    S.card ≤ 2 * N := by
  obtain ⟨θ, φ, h⟩ := hnonconstant
  apply card_stationary_angles_le p (ne_constant_of_trigonometricFunction_ne p θ φ h)
    hreal N hN S hS
  intro a ha b hb he
  obtain ⟨n, hn⟩ := (finitePhase_eq_iff a b).mp he
  exact hperiod a ha b hb n hn

end
end Surreal.Surcomplex
