import Surreal.Algebra.LaurentCayley
import Surreal.Algebra.ComplexPolynomialRealPart
import Surreal.Surcomplex.CayleyInfinitesimal
import Surreal.Surcomplex.Valuation

/-!
# Exact Cayley numerators for actual trigonometric polynomials

For `trigonometry:thm:stability`, a Mathlib Laurent polynomial evaluated on
actual finite-angle phases pulls back to a real polynomial divided by a
positive real polynomial. The denominator has constant term one and linear
term zero. Finiteness is proved for every numerator coefficient.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Polynomial
open scoped BigOperators

noncomputable section

/-- The unit associated to the phase of an actual finite angle. -/
def phaseUnit (a : SignSequence.FiniteElement.{u}) : Surcomplex.{u}ˣ :=
  Unitary.toUnits (finitePhaseHom (Multiplicative.ofAdd a))

@[simp] theorem phaseUnit_val (a : SignSequence.FiniteElement.{u}) :
    (phaseUnit a).val = finitePhase a := rfl

/-- A finite Fourier sum, using Mathlib's Laurent-polynomial evaluation. -/
def trigonometricPolynomial (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) : Surcomplex.{u} := p.smeval (phaseUnit a)

/-- The formal angular derivative of the real part, computed by Fourier frequencies. -/
def trigonometricFourierDerivative (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) : SignSequence.{u} :=
  (∑ k ∈ p.coeff.support, p.coeff k * (phaseUnit a ^ k).val * ((k : Surcomplex.{u}) * I)).re

/-- The linear coefficient in the unscaled half-angle chart. -/
def cayleyLinear : Surcomplex.{u} := I * ofReal (1 / 2)

private theorem cayleyLinear_eq : (cayleyLinear : Surcomplex.{u}) = ofComplex (Complex.I / 2) := by
  rw [cayleyLinear, map_div₀ ofReal, map_div₀ ofComplex, ofComplex_I,
    map_one, map_ofNat ofReal, map_ofNat ofComplex]
  ring

/-- The real numerator in the local variable `x = 2 tan(h/2)`. -/
def trigonometricNumerator (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ) : Polynomial SignSequence.{u} :=
  Complexify.realPartPolynomial (LaurentCayley.numerator p (phaseUnit a) cayleyLinear N)

/-- The real part of the Laurent polynomial in the exact local Cayley chart. -/
def trigonometricCayley (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (x : SignSequence.{u}) : SignSequence.{u} :=
  (p.smeval (phaseUnit a * Unitary.toUnits
    (⟨cayley (x / 2), (mem_unitCircle_iff _).mpr (modulus_cayley _)⟩ : UnitCircle))).re

/-- Adding trigonometric polynomials adds their real numerators. -/
theorem trigonometricNumerator_add (p q : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ) :
    trigonometricNumerator (p + q) a N =
      trigonometricNumerator p a N + trigonometricNumerator q a N := by
  rw [trigonometricNumerator, LaurentCayley.numerator_add,
    Complexify.realPartPolynomial_add]
  rfl

/-- The shared positive denominator in the same local variable. -/
def trigonometricDenominator (N : ℕ) : Polynomial SignSequence.{u} :=
  (1 + C (1 / 4) * X ^ 2) ^ N

/-- Each phase power remains finite, including negative frequencies. -/
theorem isFinite_phaseUnit_zpow (a : SignSequence.FiniteElement.{u}) (k : ℤ) :
    IsFinite ((phaseUnit a ^ k).val) := by
  simpa only [phaseUnit, ← map_zpow, Unitary.val_toUnits_apply] using
    isFinite_unitCircle ((finitePhaseHom (Multiplicative.ofAdd a)) ^ k)

/-- Finiteness survives clearing all Laurent denominators. -/
theorem trigonometricNumerator_finite (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ)
    (hp : ∀ k ∈ p.coeff.support, IsFinite (p.coeff k)) (j : ℕ) :
    SignSequence.IsFinite ((trigonometricNumerator p a N).coeff j) := by
  have hc : IsFinite (cayleyLinear : Surcomplex.{u}) := by
    rw [cayleyLinear_eq]
    exact finite_ofComplex _
  rw [trigonometricNumerator, Complexify.realPartPolynomial_coeff]
  exact (LaurentCayley.numerator_coeff_mem finiteSubring p (phaseUnit a) cayleyLinear N hc
    hp (isFinite_phaseUnit_zpow a) j).1

/-- Clearing denominators preserves every coefficient valuation lower bound.
The bound is any surreal exponent, with no rank restriction. -/
theorem trigonometricNumerator_valuation (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ) (s : SignSequence.{u})
    (hp : ∀ k ∈ p.coeff.support, (s : WithTop SignSequence.{u}) ≤ valuation (p.coeff k))
    (j : ℕ) :
    (s : WithTop SignSequence.{u}) ≤
      SignSequence.valuation ((trigonometricNumerator p a N).coeff j) := by
  rw [trigonometricNumerator, Complexify.realPartPolynomial_coeff]
  have hc : IsFinite (cayleyLinear : Surcomplex.{u}) := by
    rw [cayleyLinear_eq]
    exact finite_ofComplex _
  have hv : (s : WithTop SignSequence.{u}) ≤
      valuation ((LaurentCayley.numerator p (phaseUnit a) cayleyLinear N).coeff j) := by
    simp only [LaurentCayley.numerator, Finsupp.sum, finsetSum_coeff, coeff_C_mul]
    apply valuation.map_le_sum
    intro k hk
    have hf : IsFinite ((phaseUnit a ^ k).val * (LaurentCayley.frequency cayleyLinear N k).coeff j) :=
      finiteSubring.mul_mem (isFinite_phaseUnit_zpow a k)
        (LaurentCayley.frequency_coeff_mem finiteSubring cayleyLinear hc N k j)
    rw [mul_assoc, valuation_mul]
    exact (hp k hk).trans (le_add_of_nonneg_right ((isFinite_iff_valuation_nonneg _).mp hf))
  exact hv.trans (by rw [valuation_eq_min_coordinates]; exact min_le_left _ _)

/-- The real numerator preserves the center value. -/
theorem trigonometricNumerator_coeff_zero (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ) :
    (trigonometricNumerator p a N).coeff 0 = (trigonometricPolynomial p a).re := by
  rw [trigonometricNumerator, Complexify.realPartPolynomial_coeff,
    LaurentCayley.numerator_coeff_zero]
  rfl

/-- The linear coefficient is exactly the real part of the Fourier derivative sum. -/
theorem trigonometricNumerator_coeff_one (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    (trigonometricNumerator p a N).coeff 1 = trigonometricFourierDerivative p a := by
  unfold trigonometricFourierDerivative
  rw [trigonometricNumerator, Complexify.realPartPolynomial_coeff,
    LaurentCayley.numerator_coeff_one p (phaseUnit a) cayleyLinear N hN]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [cayleyLinear, map_div₀, map_one, map_ofNat]
  field_simp

@[simp] theorem trigonometricDenominator_coeff_zero (N : ℕ) :
    (trigonometricDenominator N : Polynomial SignSequence.{u}).coeff 0 = 1 := by
  simp [trigonometricDenominator, coeff_zero_eq_eval_zero]

/-- The denominator never vanishes at an actual real parameter. -/
theorem trigonometricDenominator_eval_pos (N : ℕ) (x : SignSequence.{u}) :
    0 < (trigonometricDenominator N).eval x := by
  simp only [trigonometricDenominator, eval_pow, eval_add, eval_one, eval_mul, eval_C, eval_X]
  positivity

private theorem cayleyLinear_mul (x : SignSequence.{u}) :
    cayleyLinear * ofReal x = I * ofReal (x / 2) := by
  rw [cayleyLinear, mul_assoc, ← map_mul]
  congr 2
  ring

private theorem cayley_plus_ne_zero (x : SignSequence.{u}) :
    1 + cayleyLinear * ofReal x ≠ 0 := by
  intro h
  have he := congrArg (fun z : Surcomplex.{u} => z.re) h
  rw [cayleyLinear_mul] at he
  norm_num [QuadraticAlgebra.re_one] at he

private theorem cayley_minus_ne_zero (x : SignSequence.{u}) :
    1 - cayleyLinear * ofReal x ≠ 0 := by
  intro h
  have he := congrArg (fun z : Surcomplex.{u} => z.re) h
  rw [cayleyLinear_mul] at he
  norm_num [QuadraticAlgebra.re_one] at he

/-- The generic cleared denominator is the image of the real positive denominator. -/
theorem cayley_denominator_eval (N : ℕ) (x : SignSequence.{u}) :
    (LaurentCayley.denominator cayleyLinear N).eval (ofReal x) =
      ofReal ((trigonometricDenominator N).eval x) := by
  simp only [LaurentCayley.denominator, trigonometricDenominator, eval_pow, eval_mul,
    eval_add, eval_sub, eval_one, eval_C, eval_X, map_pow]
  congr 1
  rw [cayleyLinear_mul]
  simp only [map_add, map_one, map_mul, map_div₀, map_ofNat, map_pow]
  field_simp
  linear_combination -4 * ofReal x ^ 2 * I_sq.{u}

/-- The exact rational pullback, valid even for noninfinitesimal real parameters. -/
theorem eval_trigonometricNumerator (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (x : SignSequence.{u}) :
    (trigonometricNumerator p a N).eval x =
      (trigonometricDenominator N).eval x *
        (p.smeval (phaseUnit a * Unitary.toUnits
          (⟨cayley (x / 2), (mem_unitCircle_iff _).mpr (modulus_cayley _)⟩ : UnitCircle))).re := by
  rw [trigonometricNumerator, Complexify.eval_realPartPolynomial]
  change (Polynomial.eval (ofReal x)
    (LaurentCayley.numerator p (phaseUnit a) cayleyLinear N)).re = _
  rw [LaurentCayley.eval_numerator p (phaseUnit a) cayleyLinear (ofReal x) N hN
    (cayley_plus_ne_zero x) (cayley_minus_ne_zero x), cayley_denominator_eval]
  have he : Units.mk0 ((1 + cayleyLinear * ofReal x) / (1 - cayleyLinear * ofReal x))
      (div_ne_zero (cayley_plus_ne_zero x) (cayley_minus_ne_zero x)) =
      Unitary.toUnits (⟨cayley (x / 2),
        (mem_unitCircle_iff _).mpr (modulus_cayley _)⟩ : UnitCircle) := by
    apply Units.ext
    simp only [Units.val_mk0, Unitary.val_toUnits_apply]
    rw [cayleyLinear_mul, cayley_eq_fraction]
  rw [he]
  simp

/-- Clearing the positive denominator neither introduces nor removes real roots. -/
theorem isRoot_trigonometricNumerator_iff (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (x : SignSequence.{u}) :
    (trigonometricNumerator p a N).IsRoot x ↔ trigonometricCayley p a x = 0 := by
  change (trigonometricNumerator p a N).eval x = 0 ↔ _
  rw [eval_trigonometricNumerator p a N hN x]
  change (trigonometricDenominator N).eval x * trigonometricCayley p a x = 0 ↔ _
  exact mul_eq_zero.trans (or_iff_right (trigonometricDenominator_eval_pos N x).ne')

/-- The rational chart is the actual angle shift wherever the half-angle chart applies. -/
theorem trigonometricCayley_two_tan_half (p : LaurentPolynomial Surcomplex.{u})
    (a h : SignSequence.FiniteElement.{u}) (hh : finitePhase h ≠ -1) :
    trigonometricCayley p a (2 * finiteTan (finiteHalf h)) =
      (trigonometricPolynomial p (a + h)).re := by
  unfold trigonometricCayley trigonometricPolynomial
  congr 2
  apply Units.ext
  simp only [Units.val_mul, Unitary.val_toUnits_apply, phaseUnit_val]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : SignSequence.{u}) ≠ 0),
    cayley_finiteTan_half h hh, finitePhase_add]

/-- A shared frequency bound also bounds a sum of Laurent polynomials. -/
theorem trigonometric_frequency_bound_add (p q : LaurentPolynomial Surcomplex.{u}) (N : ℕ)
    (hp : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (hq : ∀ k ∈ q.coeff.support, k.natAbs ≤ N) :
    ∀ k ∈ (p + q).coeff.support, k.natAbs ≤ N := by
  intro k hk
  change k ∈ (p.coeff + q.coeff).support at hk
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with h | h
  · exact hp k h
  · exact hq k h

end
end Surreal.Surcomplex
