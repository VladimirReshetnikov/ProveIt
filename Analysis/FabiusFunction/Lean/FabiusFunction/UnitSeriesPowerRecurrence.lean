import FabiusFunction.CoefficientRules
import FabiusFunction.FallingFactorialSeries
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Triangular coefficient recurrence for arbitrary formal powers

The differential equation `F G' = β F' G` gives a denominator-free recurrence
over every commutative ring. Its Euler-derivative form keeps the degree index
unchanged: `[X^n] X H' = n [X^n] H`. Splitting off the constant coefficient
of `F` leaves only lower coefficients of `G` on the right.

For `F(0) = 1` over a commutative rational algebra, substitution in the
falling-factorial series defines the formal power `F^β` and proves the
differential equation. The resulting recurrence is precisely
`eq:merged-alg-power` in the coefficient-calculus manuscript. No convergence
or choice of an analytic branch is involved.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section CommRing

variable {R : Type*} [CommRing R]

private theorem coeff_eulerDerivative (F : R⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX R F) = (n : R) * coeff n F := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative_eq, Nat.cast_succ]

/-- The differential equation `F G' = β F' G` gives a triangular,
denominator-free coefficient recurrence over any commutative ring. The
constant coefficient of `F` need not be one or even invertible. -/
theorem coeff_recurrence_of_mul_derivative_eq {F G : R⟦X⟧} (β : R)
    (h : F * d⁄dX R G = PowerSeries.C β * d⁄dX R F * G) (n : ℕ) :
    (n : R) * coeff 0 F * coeff n G =
      ∑ j ∈ Icc 1 n, ((β + 1) * (j : R) - (n : R)) *
        coeff j F * coeff (n - j) G := by
  have heuler : PowerSeries.C β * ((X * d⁄dX R F) * G) -
      F * (X * d⁄dX R G) = 0 := by
    linear_combination -X * h
  have hc := congrArg (coeff n) heuler
  rw [map_sub, coeff_C_mul, coeff_mul_eq_sum_range,
    coeff_mul_eq_sum_range] at hc
  simp only [coeff_eulerDerivative, map_zero] at hc
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib] at hc
  have hsum : (∑ j ∈ range (n + 1),
      ((β + 1) * (j : R) - (n : R)) * coeff j F * coeff (n - j) G) = 0 := by
    calc
      _ = ∑ j ∈ range (n + 1),
          (β * ((j : R) * coeff j F * coeff (n - j) G) -
            coeff j F * ((n - j : ℕ) * coeff (n - j) G)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.cast_sub (Nat.le_of_lt_succ (mem_range.mp hj))]
        ring
      _ = 0 := hc
  rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos n)] at hsum
  simp only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc,
    Nat.cast_zero, mul_zero, zero_sub, Nat.sub_zero] at hsum
  linear_combination -hsum

end CommRing

section RationalAlgebra

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The formal binomial power of a unit-constant series satisfies
`F (F^β)' = β F' F^β`. This is substitution and the chain rule applied to
the defining differential equation for the falling-factorial series. -/
theorem mul_derivative_fallingSeries_subst_sub_one
    {F : A⟦X⟧} (hF : constantCoeff F = 1) (β : A) :
    F * d⁄dX A ((fallingSeries A β).subst (F - 1)) =
      PowerSeries.C β * d⁄dX A F * (fallingSeries A β).subst (F - 1) := by
  have hs : HasSubst (F - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp [hF])
  have h := congrArg (fun H : A⟦X⟧ => H.subst (F - 1))
    (one_add_X_mul_derivative_fallingSeries A β)
  simp only [subst_mul hs, subst_add hs, subst_X hs, subst_C] at h
  have hleft : (1 : A⟦X⟧).subst (F - 1) + (F - 1) = F := by
    rw [← coe_substAlgHom hs, map_one]
    ring
  rw [hleft] at h
  change F * ((d⁄dX A (fallingSeries A β)).subst (F - 1)) =
    PowerSeries.C β * (fallingSeries A β).subst (F - 1) at h
  rw [derivative_subst A hs, map_sub]
  simp only [Derivation.map_one_eq_zero, sub_zero]
  linear_combination (d⁄dX A F) * h

/-- **`eq:merged-alg-power`.** If `F(0) = 1`, the coefficients of the formal
power `F^β` satisfy `n c_n = ∑_{j=1}^n ((β+1)j-n) a_j c_{n-j}`.
At degree zero both sides vanish; the constant coefficient is separately
one by `constantCoeff_fallingSeries` and the constant-coefficient substitution rule. -/
theorem coeff_fallingSeries_subst_sub_one_recurrence
    {F : A⟦X⟧} (hF : constantCoeff F = 1) (β : A) (n : ℕ) :
    (n : A) * coeff n ((fallingSeries A β).subst (F - 1)) =
      ∑ j ∈ Icc 1 n, ((β + 1) * (j : A) - (n : A)) * coeff j F *
        coeff (n - j) ((fallingSeries A β).subst (F - 1)) := by
  simpa only [coeff_zero_eq_constantCoeff_apply, hF, mul_one] using
    coeff_recurrence_of_mul_derivative_eq β
      (mul_derivative_fallingSeries_subst_sub_one A hF β) n

end RationalAlgebra

end Fabius
