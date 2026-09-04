import FabiusFunction.ExponentialRescaling
import FabiusFunction.LagrangeInversion
import FabiusFunction.StirlingFirstReverse

/-!
# Abel polynomials from Lagrange inversion

The Abel polynomials are `A₀(a,x) = 1` and
`Aₙ₊₁(a,x) = x (x - (n+1) a)^n`.  Their generating function is

`exp(x T(t)) = ∑ Aₙ(a,x) tⁿ/n!`, where `T = t exp(-a T)`.

The series `abelSeries a` is constructed by the existing compositional-inverse
construction, with `exp(a t)` the proved multiplicative inverse of `exp(-a t)`.
The coefficient theorem also applies to *any* series satisfying the displayed
functional equation.  Thus the result neither assumes the desired coefficients
nor restricts the manuscript's arbitrary solution to a chosen construction.

The proof is the Lagrange–Bürmann formula with outer function `exp(x t)`.
Its derivative contributes `x`, and the remaining exponential has parameter
`x - (n+1) a`.  The binomial identity follows by multiplying the two generating
functions.  All identities hold over any commutative rational algebra; the
polynomials themselves are defined over every commutative ring.

## Main declarations

* `abelPolynomial`, `abelPolynomial_zero`, `abelPolynomial_succ`,
  `abelPolynomial_succ_eval` give the polynomials, including degree zero.
* `abelSeries`, `abelSeries_eq`, `hasSubst_abelSeries` construct the solution.
* `abel_eq_zero_and_one` shows every solution has constant coefficient zero
  and linear coefficient one.
* `coeff_exp_subst_of_abel_eq`, `exp_subst_eq_egfA_abelPolynomial` give the
  coefficients and full generating function for any solution.
* `abelPolynomial_eval_add` is the Abel binomial identity, including index zero.
-/

set_option autoImplicit false

open PowerSeries

noncomputable section

namespace Fabius

section Polynomials

variable {A : Type*} [CommRing A]

/-- The Abel polynomials: `A₀(a,X) = 1` and
`Aₙ₊₁(a,X) = X (X - (n+1) a)^n`. -/
def abelPolynomial (a : A) : ℕ → Polynomial A
  | 0 => 1
  | n + 1 => Polynomial.X *
      (Polynomial.X - Polynomial.C (((n + 1 : ℕ) : A) * a)) ^ n

/-- The zeroth Abel polynomial is one, including when the parameter is zero. -/
@[simp] theorem abelPolynomial_zero (a : A) : abelPolynomial a 0 = 1 := rfl

/-- The closed polynomial formula in every positive degree. -/
theorem abelPolynomial_succ (a : A) (n : ℕ) :
    abelPolynomial a (n + 1) = Polynomial.X *
      (Polynomial.X - Polynomial.C (((n + 1 : ℕ) : A) * a)) ^ n := rfl

/-- Evaluating the positive-degree Abel polynomial gives
`Aₙ₊₁(a,x) = x (x - (n+1) a)^n`. -/
theorem abelPolynomial_succ_eval (a x : A) (n : ℕ) :
    (abelPolynomial a (n + 1)).eval x = x * (x - ((n + 1 : ℕ) : A) * a) ^ n := by
  simp only [abelPolynomial_succ, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C]

end Polynomials

section Series

variable {A : Type*} [CommRing A] [Algebra ℚ A]

private theorem rescale_neg_exp_mul (a : A) :
    rescale (-a) (exp A) * rescale a (exp A) = 1 := by
  rw [exp_mul_exp_eq_exp_add, neg_add_cancel, rescale_zero_exp]

private theorem rescale_exp_pow (a : A) (n : ℕ) :
    rescale a (exp A) ^ n = rescale ((n : A) * a) (exp A) := by
  rw [← map_pow, exp_pow_eq_rescale_exp, rescale_rescale]

/-- The canonical Abel series, constructed as the compositional inverse of
`t exp(a t)`, so that `T = t exp(-a T)`. -/
def abelSeries (a : A) : A⟦X⟧ :=
  Lagrange.solution (rescale (-a) (exp A)) (rescale a (exp A)) (rescale_neg_exp_mul a)

/-- The canonical Abel series satisfies its defining functional equation. -/
theorem abelSeries_eq (a : A) :
    abelSeries a = X * (rescale (-a) (exp A)).subst (abelSeries a) :=
  Lagrange.solution_eq _ _ _

/-- Substitution into the canonical Abel series is well defined. -/
theorem hasSubst_abelSeries (a : A) : HasSubst (abelSeries a) :=
  Lagrange.hasSubst_solution _ _ _

/-- Every solution of the Abel functional equation has zero constant term
and unit linear coefficient.  In particular, it is a delta series. -/
theorem abel_eq_zero_and_one (a : A) {T : A⟦X⟧}
    (hT : T = X * (rescale (-a) (exp A)).subst T) :
    constantCoeff T = 0 ∧ coeff 1 T = 1 := by
  have hzero := Lagrange.constantCoeff_eq_zero_of_eq_X_mul hT
  refine ⟨hzero, ?_⟩
  rw [hT, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_subst_of_constantCoeff_eq_zero A hzero,
    ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_exp]

/-- Lagrange inversion gives the explicit Abel coefficient for any solution
`T = t exp(-a T)`: `[t^(n+1)] exp(x T) = x (x-(n+1)a)^n/(n+1)!`. -/
theorem coeff_exp_subst_of_abel_eq (a x : A) {T : A⟦X⟧}
    (hT : T = X * (rescale (-a) (exp A)).subst T) (n : ℕ) :
    coeff (n + 1) ((rescale x (exp A)).subst T) =
      algebraMap ℚ A (1 / (n + 1).factorial) *
        (x * (x - ((n + 1 : ℕ) : A) * a) ^ n) := by
  have hs : HasSubst T := Lagrange.hasSubst_of_eq_X_mul hT
  have hinverse :
      (rescale (-a) (exp A)).subst T * (rescale a (exp A)).subst T = 1 := by
    rw [← subst_mul hs, rescale_neg_exp_mul, ← coe_substAlgHom hs, map_one]
  have h := Lagrange.coeff_subst_derivative hT rfl hinverse
    (rescale x (exp A)) (n + 1) (by omega)
  rw [Nat.add_sub_cancel, derivative_rescale_exp, rescale_exp_pow,
    mul_assoc, exp_mul_exp_eq_exp_add,
    show x + ((n + 1 : ℕ) : A) * (-a) = x - ((n + 1 : ℕ) : A) * a by ring,
    coeff_C_mul, coeff_rescale, coeff_exp] at h
  have hcancel :
      algebraMap ℚ A (1 / ((n + 1 : ℕ) : ℚ)) * ((n + 1 : ℕ) : A) = 1 := by
    rw [← map_natCast (algebraMap ℚ A) (n + 1), ← map_mul,
      one_div_mul_cancel (by positivity), map_one]
  have hfactorial :
      algebraMap ℚ A (1 / ((n + 1 : ℕ) : ℚ)) *
        algebraMap ℚ A (1 / n.factorial) =
      algebraMap ℚ A (1 / (n + 1).factorial) := by
    rw [← map_mul, one_div_mul_one_div, Nat.factorial_succ, Nat.cast_mul]
  calc
    coeff (n + 1) ((rescale x (exp A)).subst T) =
        algebraMap ℚ A (1 / ((n + 1 : ℕ) : ℚ)) *
          (((n + 1 : ℕ) : A) * coeff (n + 1) ((rescale x (exp A)).subst T)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = algebraMap ℚ A (1 / ((n + 1 : ℕ) : ℚ)) *
          (x * ((x - ((n + 1 : ℕ) : A) * a) ^ n *
            algebraMap ℚ A (1 / n.factorial))) := by rw [h]
    _ = (algebraMap ℚ A (1 / ((n + 1 : ℕ) : ℚ)) *
          algebraMap ℚ A (1 / n.factorial)) *
          (x * (x - ((n + 1 : ℕ) : A) * a) ^ n) := by ring
    _ = _ := by rw [hfactorial]

/-- The full Abel exponential generating function for any solution of
`T = t exp(-a T)`, including its constant coefficient. -/
theorem exp_subst_eq_egfA_abelPolynomial (a x : A) {T : A⟦X⟧}
    (hT : T = X * (rescale (-a) (exp A)).subst T) :
    (rescale x (exp A)).subst T =
      egfA A (fun n => (abelPolynomial a n).eval x) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      have hconstant : constantCoeff ((rescale x (exp A)).subst T) = 1 := by
        rw [constantCoeff_subst_of_constantCoeff_eq_zero A
            (Lagrange.constantCoeff_eq_zero_of_eq_X_mul hT),
          ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
          coeff_zero_eq_constantCoeff_apply, constantCoeff_exp]
      simpa only [coeff_zero_eq_constantCoeff_apply, constantCoeff_egfA,
        abelPolynomial_zero, Polynomial.eval_one] using hconstant
  | succ n =>
      rw [coeff_exp_subst_of_abel_eq a x hT n, coeff_egfA, abelPolynomial_succ_eval]

/-- The Abel polynomials form a sequence of binomial type.  This is valid
at index zero and for every parameter, including `a = 0`. -/
theorem abelPolynomial_eval_add (a x y : A) (n : ℕ) :
    (abelPolynomial a n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : A) *
        ((abelPolynomial a k).eval x * (abelPolynomial a (n - k)).eval y) := by
  have h : egfA A (fun n => (abelPolynomial a n).eval (x + y)) =
      egfA A (Bell.binomialConv (fun n => (abelPolynomial a n).eval x)
        (fun n => (abelPolynomial a n).eval y)) := by
    rw [← egfA_mul,
      ← exp_subst_eq_egfA_abelPolynomial a (x + y) (abelSeries_eq a),
      ← exp_subst_eq_egfA_abelPolynomial a x (abelSeries_eq a),
      ← exp_subst_eq_egfA_abelPolynomial a y (abelSeries_eq a),
      ← subst_mul (hasSubst_abelSeries a), exp_mul_exp_eq_exp_add]
  have hn := congrFun (seq_eq_of_egfA_eq A h) n
  rw [Bell.binomialConv_eq_sum_range] at hn
  exact hn

end Series

end Fabius
