import Surreal.Algebra.Complexify
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Real parts of polynomial coefficients

The coefficientwise real part evaluates to the real part on the real axis.
This supplies a real numerator for `trigonometry:thm:stability` without
requiring a separate presentation of a real-valued Laurent polynomial.
-/

namespace Surreal.Complexify

open Polynomial

noncomputable section

variable {F : Type*} [CommRing F]

/-- Project each coefficient of a complexified polynomial to the real axis. -/
def realPartPolynomial (P : (Complexify F)[X]) : F[X] :=
  P.sum fun n a => monomial n a.re

@[simp] theorem realPartPolynomial_coeff (P : (Complexify F)[X]) (n : ℕ) :
    (realPartPolynomial P).coeff n = (P.coeff n).re := by
  classical
  simp only [realPartPolynomial, sum_def, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hn
    simp [notMem_support_iff.mp hn]

/-- Coefficientwise real projection preserves addition. -/
theorem realPartPolynomial_add (P Q : (Complexify F)[X]) :
    realPartPolynomial (P + Q) = realPartPolynomial P + realPartPolynomial Q := by
  apply Polynomial.ext
  intro n
  simp

/-- Real projection commutes with evaluation at every real scalar. -/
theorem eval_realPartPolynomial (P : (Complexify F)[X]) (x : F) :
    (realPartPolynomial P).eval x = (P.eval (algebraMap F (Complexify F) x)).re := by
  classical
  rw [realPartPolynomial, sum_def, eval_finsetSum]
  rw [eval_eq_sum, sum_def]
  change _ = (QuadraticAlgebra.reₗ (-1) 0)
    (∑ n ∈ P.support, P.coeff n * (algebraMap F (Complexify F) x) ^ n)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp [← map_pow]

end
end Surreal.Complexify
