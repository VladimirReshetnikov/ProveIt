import Surreal.Algebra.LaurentFrequencyWeight
import Surreal.Surcomplex.TrigonometricPolynomialDerivative
import Surreal.Surcomplex.TrigonometricPolynomialUniqueness

/-!
# The derivative polynomial of a finite Fourier sum

Angular differentiation multiplies the coefficient at integer frequency
`k` by `ik`. It preserves the frequency band and conjugate symmetry, and
annihilates exactly the constant Laurent polynomials. Its evaluation gives
the already proved native fine derivative, as used in
`trigonometry:cor:chebyshev`.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The native Laurent polynomial obtained by angular differentiation. -/
def angularDerivative (p : LaurentPolynomial Surcomplex.{u}) : LaurentPolynomial Surcomplex.{u} :=
  LaurentFrequency.weight p (fun k => (k : Surcomplex.{u}) * I)

@[simp] theorem coeff_angularDerivative (p : LaurentPolynomial Surcomplex.{u}) (k : ℤ) :
    (angularDerivative p).coeff k = ((k : Surcomplex.{u}) * I) * p.coeff k := rfl

/-- Angular differentiation preserves every original frequency bound. -/
theorem angularDerivative_frequency_bound (p : LaurentPolynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∀ k ∈ (angularDerivative p).coeff.support, k.natAbs ≤ N :=
  fun k hk => hN k (LaurentFrequency.support_weight_subset p _ hk)

private theorem imaginaryUnit_ne_zero : (I : Surcomplex.{u}) ≠ 0 := by
  intro h
  have hi := congrArg (fun z : Surcomplex.{u} => z.im) h
  simp at hi

/-- Angular differentiation has precisely the constant Laurent polynomials as its kernel. -/
theorem angularDerivative_eq_zero_iff (p : LaurentPolynomial Surcomplex.{u}) :
    angularDerivative p = 0 ↔ p = LaurentPolynomial.C (p.coeff 0) := by
  rw [LaurentFrequency.eq_constant_iff]
  constructor
  · intro he k hk
    have hc := congrArg (fun q : LaurentPolynomial Surcomplex.{u} => q.coeff k) he
    rw [coeff_angularDerivative] at hc
    exact (mul_eq_zero.mp hc).resolve_left
      (mul_ne_zero (by exact_mod_cast hk) imaginaryUnit_ne_zero)
  · intro h
    apply LaurentPolynomial.ext
    intro k
    change (angularDerivative p).coeff k = 0
    rw [coeff_angularDerivative]
    by_cases hk : k = 0
    · subst k
      simp
    · rw [h k hk, mul_zero]

/-- Conjugate-symmetric coefficients remain conjugate-symmetric after angular differentiation. -/
theorem angularDerivative_conjugate_symmetric (p : LaurentPolynomial Surcomplex.{u})
    (hp : ∀ k : ℤ, p.coeff (-k) = conj (p.coeff k)) :
    ∀ k : ℤ, (angularDerivative p).coeff (-k) = conj ((angularDerivative p).coeff k) := by
  intro k
  simp only [coeff_angularDerivative, Int.cast_neg, hp, map_mul, map_intCast, conj_I]
  ring

/-- Consequently the derivative polynomial is real-valued whenever the original one is. -/
theorem angularDerivative_real (p : LaurentPolynomial Surcomplex.{u})
    (hp : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0) :
    ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial (angularDerivative p) θ).im = 0 :=
  (trigonometricPolynomial_real_iff _).mpr
    (angularDerivative_conjugate_symmetric p ((trigonometricPolynomial_real_iff p).mp hp))

/-- The real part of the derivative polynomial is the existing formal Fourier derivative. -/
theorem angularDerivative_eval_re (p : LaurentPolynomial Surcomplex.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    (trigonometricPolynomial (angularDerivative p) θ).re = trigonometricFourierDerivative p θ := by
  unfold trigonometricPolynomial angularDerivative trigonometricFourierDerivative
  rw [LaurentFrequency.smeval_weight]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Evaluation of the derivative polynomial supplies the native fine derivative at every finite angle. -/
theorem fineHasDerivAt_angularDerivative (p : LaurentPolynomial Surcomplex.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (trigonometricFunction p)
      (trigonometricPolynomial (angularDerivative p) θ).re θ.val := by
  rw [angularDerivative_eval_re]
  exact fineHasDerivAt_trigonometricFunction p θ

/-- For a real polynomial, stationarity is exactly a zero of its derivative Laurent polynomial. -/
theorem stationary_iff_angularDerivative_zero (p : LaurentPolynomial Surcomplex.{u})
    (hp : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (θ : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (trigonometricFunction p) 0 θ.val ↔
      trigonometricPolynomial (angularDerivative p) θ = 0 := by
  constructor
  · intro hs
    have hr := (fineHasDerivAt_angularDerivative p θ).unique hs
    apply QuadraticAlgebra.ext
    · exact hr
    · exact angularDerivative_real p hp θ
  · intro hz
    have hd := fineHasDerivAt_angularDerivative p θ
    simpa only [hz, QuadraticAlgebra.re_zero] using hd

end
end Surreal.Surcomplex
