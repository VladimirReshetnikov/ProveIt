import FabiusFunction.FabiusLambertAllOrderAlgebra
import FabiusFunction.SaddleLogExpansionAlgebra

/-!
# Formal-log correctness of the all-order Lambert coefficients

The recursive displacement coefficients are identified with the logarithm
of the formal unit series `1 + u A(u)`.  This proves coefficientwise that
`A = a₀ + log(1 + u A) / log 2`, supplying the exact cancellations needed
to turn the formal lower-Lambert series into arbitrary-order analytic
approximations.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial

namespace Fabius

open SaddleExpansion

/-- Coefficients of `1 + u * A(u)`, where `A` is the formal Lambert
displacement. -/
noncomputable def dyadicLambertUnitSeriesCoefficient : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => dyadicLambertDisplacementPolynomial n

@[simp] theorem dyadicLambertUnitSeriesCoefficient_zero :
    dyadicLambertUnitSeriesCoefficient 0 = 1 := by rfl

@[simp] theorem dyadicLambertUnitSeriesCoefficient_succ (n : ℕ) :
    dyadicLambertUnitSeriesCoefficient (n + 1) =
      dyadicLambertDisplacementPolynomial n := by rfl

/-- Formal correctness of the recursive Lambert coefficients: positive
coefficients of `log (1 + u A(u))` are `log(2) * a_n`. -/
theorem dyadicLambert_logCoeff_succ (n : ℕ) :
    logCoeff dyadicLambertUnitSeriesCoefficient (n + 1) =
      C (Real.log 2) * dyadicLambertDisplacementPolynomial (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [logCoeff_succ, dyadicLambertUnitSeriesCoefficient_succ,
        dyadicLambertDisplacementPolynomial_succ]
      simp only [Algebra.smul_def, Polynomial.algebraMap_apply]
      have hsum :
          ∑ j ∈ range n,
              ((n - j : ℕ) : Polynomial ℝ) *
                logCoeff dyadicLambertUnitSeriesCoefficient (n - j) *
                  dyadicLambertUnitSeriesCoefficient (j + 1) =
            C (Real.log 2) *
              ∑ j : Fin n,
                C ((n - j : ℕ) : ℝ) *
                    dyadicLambertDisplacementPolynomial j *
                  dyadicLambertDisplacementPolynomial (n - j) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun j : ℕ =>
            C ((n - j : ℕ) : ℝ) *
                dyadicLambertDisplacementPolynomial j *
              dyadicLambertDisplacementPolynomial (n - j)) n]
        rw [mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < n := mem_range.1 hj
        have hpos : 0 < n - j := Nat.sub_pos_of_lt hjlt
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hm, ih m (by omega),
          dyadicLambertUnitSeriesCoefficient_succ]
        norm_num
        ring
      rw [hsum]
      have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      apply Polynomial.funext
      intro z
      simp only [eval_sub, eval_mul, eval_C, eval_finsetSum]
      norm_num
      field_simp [hL]

/-- The full formal displacement series in the inverse large parameter. -/
noncomputable def dyadicLambertDisplacementSeries :
    PowerSeries (Polynomial ℝ) :=
  PowerSeries.mk dyadicLambertDisplacementPolynomial

@[simp] theorem coeff_dyadicLambertDisplacementSeries (n : ℕ) :
    PowerSeries.coeff n dyadicLambertDisplacementSeries =
      dyadicLambertDisplacementPolynomial n := by
  rw [dyadicLambertDisplacementSeries, PowerSeries.coeff_mk]

/-- Coefficientwise form of the formal fixed-point equation
`A = a₀ + log(1 + u A) / log 2`. -/
theorem dyadicLambertDisplacementPolynomial_eq_logCoeff (n : ℕ) :
    dyadicLambertDisplacementPolynomial n =
      if n = 0 then dyadicLambertDisplacementPolynomial 0
      else C (Real.log 2)⁻¹ *
        logCoeff dyadicLambertUnitSeriesCoefficient n := by
  cases n with
  | zero => rw [if_pos rfl]
  | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rw [dyadicLambert_logCoeff_succ]
      have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      apply Polynomial.funext
      intro z
      simp only [eval_mul, eval_C]
      field_simp [hL]

/-- Scalar form of the coefficientwise fixed-point equation: at a real `ell`
the value `a_0 ell` is `ell / log 2`, while for `n ≠ 0` the value `a_n ell` is
`(log 2)⁻¹` times the value at `ell` of the `n`-th formal-log coefficient of
`1 + u A(u)`. -/
theorem dyadicLambertDisplacementCoefficient_eq_logCoeff
    (n : ℕ) (ell : ℝ) :
    dyadicLambertDisplacementCoefficient n ell =
      if n = 0 then ell / Real.log 2
      else (Real.log 2)⁻¹ *
        (logCoeff dyadicLambertUnitSeriesCoefficient n).eval ell := by
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl, dyadicLambertDisplacementCoefficient_zero]
  · rw [if_neg hn, dyadicLambertDisplacementCoefficient,
      dyadicLambertDisplacementPolynomial_eq_logCoeff, if_neg hn]
    simp only [eval_mul, eval_C]

end Fabius
