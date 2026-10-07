import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open Polynomial

variable {A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def polynomialPrimitive (p : Polynomial A) : Polynomial A :=
  p.sum fun n a => monomial (n + 1) (((n + 1 : ℕ) : ℚ)⁻¹ • a)

@[simp] theorem polynomialPrimitive_derivative (p : Polynomial A) :
    (polynomialPrimitive p).derivative = p := by
  classical
  have hcoef (n : ℕ) (a : A) :
      (((n + 1 : ℕ) : ℚ)⁻¹ • a) * ((n : A) + 1) = a := by
    rw [← Nat.cast_add_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_smul]
  simp only [polynomialPrimitive, sum_def, derivative_sum, derivative_monomial_succ, hcoef]
  exact sum_monomial_eq p

@[simp] theorem polynomialPrimitive_eval_zero (p : Polynomial A) :
    (polynomialPrimitive p).eval 0 = 0 := by
  classical
  simp only [polynomialPrimitive, sum_def, eval_finsetSum, eval_monomial]
  simp

omit [Algebra ℚ A] in
theorem polynomial_eq_of_derivative_of_eval_zero [IsAddTorsionFree A]
    {p q : Polynomial A} (hderiv : p.derivative = q.derivative)
    (hzero : p.eval 0 = q.eval 0) : p = q := by
  have hd : (p - q).derivative = 0 := by rw [derivative_sub, hderiv, sub_self]
  have hconst := eq_C_of_derivative_eq_zero hd
  have hz : (p - q).coeff 0 = 0 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_sub, sub_eq_zero] using hzero
  rw [hz, map_zero] at hconst
  exact sub_eq_zero.mp hconst

theorem polynomialPrimitive_unique [IsAddTorsionFree A]
    {p q : Polynomial A} (hderiv : q.derivative = p) (hzero : q.eval 0 = 0) :
    polynomialPrimitive p = q := by
  apply polynomial_eq_of_derivative_of_eval_zero
  · simpa using hderiv.symm
  · simpa using hzero.symm

end Erdos3

end

end OAI
