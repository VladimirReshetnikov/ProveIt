import Surreal.Algebra.PolynomialHomogeneousTransform
import Surreal.Surcomplex.Cayley

/-!
# The polynomial Cayley transform of a spectral factor

The literal polynomial in `trigonometry:eq:fejerconstruction` is obtained
by evaluating Mathlib's homogenization at two linear coordinates.
Its degree bound and exact values hold at every actual surreal parameter.
-/

universe u
namespace Surreal.Surcomplex.CayleySpectral

open Foundations Polynomial

noncomputable section

/-- First homogeneous coordinate of the inverse Cayley substitution. -/
def first : Polynomial Surcomplex.{u} := C (-I / 2) * (X - 1)

/-- Second homogeneous coordinate of the inverse Cayley substitution. -/
def second : Polynomial Surcomplex.{u} := C (1 / 2) * (X + 1)

/-- The manuscript's polynomial `( (1+U)/2 )^N q((U-1)/(i(U+1)))`. -/
def factor (q : Polynomial Surcomplex.{u}) (N : ℕ) : Polynomial Surcomplex.{u} :=
  PolynomialHomogeneousTransform.transform q N first second

/-- The construction preserves the bound on the factor degree. -/
theorem natDegree_factor_le (q : Polynomial Surcomplex.{u}) (N : ℕ) (hq : q.natDegree ≤ N) :
    (factor q N).natDegree ≤ N := by
  apply PolynomialHomogeneousTransform.natDegree_transform_le q N hq
  · exact (natDegree_C_mul_le _ _).trans
      ((natDegree_sub_le _ _).trans (max_le natDegree_X_le (by simp)))
  · exact (natDegree_C_mul_le _ _).trans
      (natDegree_add_le_of_degree_le natDegree_X_le (by simp))

private theorem denominator_ne_zero (t : SignSequence.{u}) : 1 - I * ofReal t ≠ 0 := by
  intro he
  have hr := congrArg (fun z : Surcomplex.{u} => z.re) he
  norm_num [Complexify.mul_re, QuadraticAlgebra.re_one] at hr

/-- The second coordinate on the circle is the reciprocal Cayley denominator. -/
theorem second_eval_cayley (t : SignSequence.{u}) :
    second.eval (cayley t) = (1 - I * ofReal t)⁻¹ := by
  simp only [second, eval_mul, eval_C, eval_add, eval_X, eval_one, cayley_eq_fraction]
  field_simp [denominator_ne_zero t]
  ring

/-- The first coordinate divided by the second recovers the original real parameter. -/
theorem first_eval_cayley (t : SignSequence.{u}) :
    first.eval (cayley t) = ofReal t * second.eval (cayley t) := by
  rw [second_eval_cayley]
  simp only [first, eval_mul, eval_C, eval_sub, eval_X, eval_one, cayley_eq_fraction]
  field_simp [denominator_ne_zero t]
  linear_combination -2 * ofReal t * I_sq.{u}

/-- Exact evaluation of the constructed polynomial at every actual Cayley point. -/
theorem eval_factor_cayley (q : Polynomial Surcomplex.{u}) (N : ℕ) (hq : q.natDegree ≤ N)
    (t : SignSequence.{u}) :
    (factor q N).eval (cayley t) = q.eval (ofReal t) * ((1 - I * ofReal t)⁻¹) ^ N := by
  rw [factor, PolynomialHomogeneousTransform.eval_transform_of_mul q N hq first second
    (cayley t) (ofReal t) (first_eval_cayley t), second_eval_cayley]


/-- The squared-modulus identity cancels exactly the positive cleared denominator. -/
theorem modulus_sq_factor_cayley_mul (q : Polynomial Surcomplex.{u}) (N : ℕ)
    (hq : q.natDegree ≤ N) (t : SignSequence.{u}) :
    modulus ((factor q N).eval (cayley t)) ^ 2 * (1 + t ^ 2) ^ N =
      modulus (q.eval (ofReal t)) ^ 2 := by
  rw [eval_factor_cayley q N hq t, modulus_mul]
  have hm : modulus (((1 - I * ofReal t)⁻¹) ^ N) =
      ((modulus (1 - I * ofReal t))⁻¹) ^ N := by
    change modulusMonoidWithZeroHom _ = _
    rw [map_pow]
    exact congrArg (fun x => x ^ N) (modulus_inv _)
  rw [hm, mul_pow, ← pow_mul, Nat.mul_comm N 2, pow_mul, inv_pow, modulus_sq]
  have hd : normSq (1 - I * ofReal t) = 1 + t ^ 2 := by
    simp [normSq_eq, pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  simp only [modulus_sq]
  rw [hd]
  have hn : (1 + t ^ 2) ≠ 0 := ne_of_gt (by positivity)
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hn, one_pow, mul_one]

end
end Surreal.Surcomplex.CayleySpectral
