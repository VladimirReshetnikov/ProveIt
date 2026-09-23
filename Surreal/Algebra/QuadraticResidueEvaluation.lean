import Surreal.Algebra.QuadraticResidueAlgebra

/-!
# Evaluation formulas for the quadratic residue functional

The separated-root and double-root formulas in
`trigonometry:thm:residuepairing` and `trigonometry:eq:residuesum`.
Polynomial representatives have arbitrary degree: monic division preserves
evaluation at either root, and at the double root it preserves the first
derivative as well. The double-root formula holds over any nontrivial
commutative ring. The separated formula requires only a field in which two
is nonzero, with an explicitly supplied square root of the parameter.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

section Ring

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Reduction modulo `X² - d` preserves evaluation at every square root
of `d`, and the value is the linear remainder evaluated at that root. -/
theorem quadratic_eval_eq_remainder_coordinates (d s : R) (hs : s ^ 2 = d)
    (g : R[X]) :
    g.eval s = (g %ₘ quadraticPolynomial d).coeff 0 +
      (g %ₘ quadraticPolynomial d).coeff 1 * s := by
  have h := congrArg (Polynomial.eval s) (modByMonic_add_div g (quadraticPolynomial d))
  have hroot : (quadraticPolynomial d).eval s = 0 := by
    simp [quadraticPolynomial, hs]
  rw [eval_add, eval_mul, hroot, zero_mul, add_zero, quadratic_remainder_eq] at h
  simpa using h.symm

/-- At the double root, the constant coordinate is evaluation at zero. -/
theorem quadratic_remainder_zero_coeff_zero (g : R[X]) :
    (g %ₘ quadraticPolynomial (0 : R)).coeff 0 = g.eval 0 := by
  simpa using (quadratic_eval_eq_remainder_coordinates 0 0 (by simp) g).symm

/-- A double factor does not change the derivative evaluated at its root. -/
theorem quadratic_remainder_zero_coeff_one (g : R[X]) :
    (g %ₘ quadraticPolynomial (0 : R)).coeff 1 = g.derivative.eval 0 := by
  have h := congrArg (fun p : R[X] => p.derivative.eval 0)
    (modByMonic_add_div g (quadraticPolynomial (0 : R)))
  rw [quadratic_remainder_eq] at h
  simpa [quadraticPolynomial, derivative_mul, derivative_X_pow] using h

/-- The unique representative at the collision is the first Taylor jet,
with no factorial or characteristic restriction. -/
theorem quadratic_remainder_zero (g : R[X]) :
    g %ₘ quadraticPolynomial (0 : R) = C (g.eval 0) + C (g.derivative.eval 0) * X := by
  rw [quadratic_remainder_eq, quadratic_remainder_zero_coeff_zero,
    quadratic_remainder_zero_coeff_one]

/-- Uniqueness of the two Taylor coefficients in the double-root remainder. -/
theorem quadratic_remainder_zero_eq_iff (g : R[X]) (a b : R) :
    g %ₘ quadraticPolynomial (0 : R) = C a + C b * X ↔
      a = g.eval 0 ∧ b = g.derivative.eval 0 := by
  rw [quadratic_remainder_zero]
  constructor
  · intro h
    constructor
    · have h0 := congrArg (fun p : R[X] => p.coeff 0) h
      simpa using h0.symm
    · have h1 := congrArg (fun p : R[X] => p.coeff 1) h
      simpa using h1.symm
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The residue functional at the collision is exactly the first derivative
at zero, as asserted in `trigonometry:thm:residuepairing`. -/
theorem quadraticResidue_mk_zero (g : R[X]) :
    quadraticResidue (0 : R) (AdjoinRoot.mk (quadraticPolynomial 0) g) =
      g.derivative.eval 0 := by
  rw [quadraticResidue_mk, quadratic_remainder_zero_coeff_one]

/-- Evaluation is the constant coordinate of the double-root quotient. -/
theorem quadraticConstant_mk_zero (g : R[X]) :
    quadraticConstant (0 : R) (AdjoinRoot.mk (quadraticPolynomial 0) g) = g.eval 0 := by
  rw [quadraticConstant_mk, quadratic_remainder_zero_coeff_zero]

/-- The same first Taylor jet is the actual class in the nonreduced
quotient, rather than only a polynomial remainder identity. -/
theorem quadratic_mk_zero_eq_taylor (g : R[X]) :
    AdjoinRoot.mk (quadraticPolynomial (0 : R)) g =
      algebraMap R (quadraticQuotient 0) (g.eval 0) +
        algebraMap R (quadraticQuotient 0) (g.derivative.eval 0) * quadraticRoot 0 := by
  rw [quadratic_eq_scalar_add_mul_root (0 : R)
    (AdjoinRoot.mk (quadraticPolynomial 0) g), quadraticConstant_mk_zero,
    quadraticResidue_mk_zero]

end Ring

section Field

variable {K : Type*} [Field K]

/-- Away from the collision, the linear remainder coordinate is a divided
difference between the two distinct roots. -/
theorem quadraticResidue_mk_eq_divided_difference (d s : K) (hd : d ≠ 0)
    (hs : s ^ 2 = d) (htwo : (2 : K) ≠ 0) (g : K[X]) :
    quadraticResidue d (AdjoinRoot.mk (quadraticPolynomial d) g) =
      (g.eval s - g.eval (-s)) / (2 * s) := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hd
    simpa [h] using hs.symm
  rw [quadraticResidue_mk,
    quadratic_eval_eq_remainder_coordinates d s hs,
    quadratic_eval_eq_remainder_coordinates d (-s) (by simpa using hs)]
  apply (eq_div_iff (mul_ne_zero htwo hs0)).2
  ring

/-- The two simple-root contributions sum to the collision-stable residue
functional, for every polynomial representative. This is
`trigonometry:eq:residuesum`. -/
theorem quadraticResidue_mk_eq_residue_sum (d s : K) (hd : d ≠ 0)
    (hs : s ^ 2 = d) (htwo : (2 : K) ≠ 0) (g : K[X]) :
    quadraticResidue d (AdjoinRoot.mk (quadraticPolynomial d) g) =
      g.eval s / (2 * s) + g.eval (-s) / (-2 * s) := by
  rw [quadraticResidue_mk_eq_divided_difference d s hd hs htwo g]
  rw [neg_mul, div_neg, sub_div]
  ring

/-- Both expressions in the source's displayed residue-sum formula agree. -/
theorem quadratic_residue_sum_eq_divided_difference (s : K) (g : K[X]) :
    g.eval s / (2 * s) + g.eval (-s) / (-2 * s) =
      (g.eval s - g.eval (-s)) / (2 * s) := by
  rw [neg_mul, div_neg, sub_div]
  ring

end Field

end

end Surreal.FinitePolynomial
