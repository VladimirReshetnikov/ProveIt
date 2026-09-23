import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Tactic

/-!
# Polynomial substitution in homogeneous coordinates

Use Mathlib's homogenization to clear a linear fractional substitution.
The degree and evaluation formulas support the spectral-factor construction
`trigonometry:eq:fejerconstruction` in `trigonometry:thm:fejer`.
-/

namespace Surreal.PolynomialHomogeneousTransform

open Polynomial

noncomputable section
variable {R : Type*} [CommSemiring R]

/-- Substitute two polynomial coordinates in Mathlib's homogeneous polynomial. -/
def transform (p : R[X]) (N : ℕ) (A B : R[X]) : R[X] :=
  MvPolynomial.eval₂ C ![A, B] (p.homogenize N)

@[simp] theorem transform_zero (N : ℕ) (A B : R[X]) : transform 0 N A B = 0 := by
  simp [transform]

@[simp] theorem transform_add (p q : R[X]) (N : ℕ) (A B : R[X]) :
    transform (p + q) N A B = transform p N A B + transform q N A B := by
  simp [transform]

/-- One monomial becomes the corresponding homogeneous monomial in the new coordinates. -/
theorem transform_monomial (a : R) (j N : ℕ) (hj : j ≤ N) (A B : R[X]) :
    transform (monomial j a) N A B = C a * A ^ j * B ^ (N - j) := by
  simp [transform, homogenize_monomial hj, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

/-- Linear polynomial coordinates preserve the homogenization degree bound. -/
theorem natDegree_transform_le (p : R[X]) (N : ℕ) (hp : p.natDegree ≤ N)
    (A B : R[X]) (hA : A.natDegree ≤ 1) (hB : B.natDegree ≤ 1) :
    (transform p N A B).natDegree ≤ N := by
  apply Polynomial.induction_with_natDegree_le
    (fun p => (transform p N A B).natDegree ≤ N) N ?_ ?_ ?_ p hp
  · simp
  · intro j a _ hj
    rw [C_mul_X_pow_eq_monomial, transform_monomial a j N hj]
    calc
      _ ≤ (C a * A ^ j).natDegree + (B ^ (N - j)).natDegree := natDegree_mul_le
      _ ≤ j + (N - j) := by
        gcongr
        · exact (natDegree_C_mul_le _ _).trans (by simpa using natDegree_pow_le_of_le j hA)
        · simpa using natDegree_pow_le_of_le (N - j) hB
      _ = N := Nat.add_sub_of_le hj
  · intro p q _ _ hp hq
    rw [transform_add]
    exact natDegree_add_le_of_degree_le hp hq

/-- Evaluation when the first coordinate is the desired argument times the second. -/
theorem eval_transform_of_mul (p : R[X]) (N : ℕ) (hp : p.natDegree ≤ N)
    (A B : R[X]) (x t : R) (h : A.eval x = t * B.eval x) :
    (transform p N A B).eval x = p.eval t * (B.eval x) ^ N := by
  apply Polynomial.induction_with_natDegree_le
    (fun p => (transform p N A B).eval x = p.eval t * (B.eval x) ^ N) N ?_ ?_ ?_ p hp
  · simp
  · intro j a _ hj
    rw [C_mul_X_pow_eq_monomial, transform_monomial a j N hj]
    simp only [eval_mul, eval_C, eval_pow, eval_monomial, h, mul_pow]
    calc
      _ = a * t ^ j * ((B.eval x) ^ j * (B.eval x) ^ (N - j)) := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hj]
  · intro p q _ _ hp hq
    simp only [transform_add, eval_add, hp, hq, add_mul]

end

section Field
variable {K : Type*} [Field K]

/-- The usual rational-substitution formula, with the nonvanishing denominator explicit. -/
theorem eval_transform (p : K[X]) (N : ℕ) (hp : p.natDegree ≤ N)
    (A B : K[X]) (x : K) (hB : B.eval x ≠ 0) :
    (transform p N A B).eval x = p.eval (A.eval x / B.eval x) * (B.eval x) ^ N :=
  eval_transform_of_mul p N hp A B x _ (by rw [div_mul_cancel₀ _ hB])

end Field
end Surreal.PolynomialHomogeneousTransform
