import FabiusFunction.CoefficientRules
import FabiusFunction.FallingFactorialSeries

/-!
# The coefficient recurrence for an arbitrary formal power

For a series `U` with constant coefficient one, write `V = U^α` for the
formal binomial power `(fallingSeries R α).subst (U - 1)`. Its coefficients
satisfy

`n c_n = ∑_{j=1}^n ((α + 1) j - n) a_j c_{n-j}`.

This is `eq:merged-alg-power` in the combinatorial coefficient calculus.
The differential equation `U V' = α U' V` supplies the proof: multiply by
`X`, read its degree-`n` coefficient, and isolate the summand at index zero.
The coefficient extraction itself works over every commutative ring, with
arbitrary constant coefficients; its left side is then `n a_0 c_n`.
Only the construction of an arbitrary formal power, and division by a
positive coefficient index, use the rational-algebra structure.

## Main declarations

* `coeff_X_mul_derivative_series`: the Euler operator multiplies coefficient
  `n` by `n`, including degree zero.
* `natCast_mul_coeff_of_mul_derivative_eq`: the general differential-equation
  extraction, with the leading coefficient left arbitrary.
* `one_add_mul_derivative_fallingSeries_subst`: the existing binomial-series
  differential equation transported through a zero-constant substitution.
* `coeff_fallingSeries_subst_zero`, `coeff_fallingSeries_subst_recurrence`,
  and `coeff_fallingSeries_subst_recurrence_of_pos`: the initial condition,
  the all-degree cleared recurrence, and the divided positive-degree form.

All powers here are formal; no convergence or analytic logarithm branch is
asserted. No new coefficient sequence or exponential recurrence is defined.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section CoefficientExtraction

variable {R : Type*} [CommRing R]

/-- The Euler operator `X d/dX` multiplies the coefficient of degree `n` by
`n`. The formula includes degree zero without a side condition. -/
theorem coeff_X_mul_derivative_series (F : R⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX R F) = (n : R) * coeff n F := by
  cases n with
  | zero => simp only [coeff_zero_X_mul, Nat.cast_zero, zero_mul]
  | succ n =>
      rw [coeff_succ_X_mul, coeff_derivative]
      push_cast
      ring

private theorem sum_range_eq_zero_add_Icc {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    (∑ j ∈ range (n + 1), f j) = f 0 + ∑ j ∈ Icc 1 n, f j := by
  have hset : range (n + 1) = insert 0 (Icc 1 n) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]

/-- Coefficients of the equation `U V' = α U' V`, with no normalization of
the leading coefficient. This denominator-free identity holds over every
commutative ring and for every degree, including zero. -/
theorem natCast_mul_coeff_of_mul_derivative_eq
    (U V : R⟦X⟧) (α : R)
    (h : U * d⁄dX R V = PowerSeries.C α * d⁄dX R U * V) (n : ℕ) :
    (n : R) * constantCoeff U * coeff n V =
      ∑ j ∈ Icc 1 n,
        (((α + 1) * (j : R)) - (n : R)) * coeff j U * coeff (n - j) V := by
  have hX : U * (X * d⁄dX R V) =
      PowerSeries.C α * ((X * d⁄dX R U) * V) := by
    calc
      U * (X * d⁄dX R V) = X * (U * d⁄dX R V) := by ring
      _ = X * (PowerSeries.C α * d⁄dX R U * V) := by rw [h]
      _ = PowerSeries.C α * ((X * d⁄dX R U) * V) := by ring
  have hc := congrArg (coeff n) hX
  rw [coeff_mul_eq_sum_range, coeff_C_mul, coeff_mul_eq_sum_range] at hc
  simp only [coeff_X_mul_derivative_series] at hc
  rw [Finset.mul_sum, sum_range_eq_zero_add_Icc, sum_range_eq_zero_add_Icc] at hc
  simp only [Nat.sub_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add,
    coeff_zero_eq_constantCoeff_apply] at hc
  calc
    (n : R) * constantCoeff U * coeff n V =
        (∑ j ∈ Icc 1 n, α * ((j : R) * coeff j U * coeff (n - j) V)) -
          ∑ j ∈ Icc 1 n, coeff j U * ((n - j : ℕ) : R) * coeff (n - j) V := by
      simp only [mul_assoc] at hc ⊢
      linear_combination hc
    _ = ∑ j ∈ Icc 1 n,
        (α * ((j : R) * coeff j U * coeff (n - j) V) -
          coeff j U * ((n - j : ℕ) : R) * coeff (n - j) V) :=
      (Finset.sum_sub_distrib).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.cast_sub (mem_Icc.mp hj).2]
      ring

end CoefficientExtraction

section FormalPowers

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The formal power `(1+w)^α` satisfies `(1+w) V' = α w' V` whenever
`w` has zero constant coefficient. This is the binomial-series differential
equation followed by the formal chain rule. -/
theorem one_add_mul_derivative_fallingSeries_subst
    {w : R⟦X⟧} (hw : constantCoeff w = 0) (α : R) :
    (1 + w) * d⁄dX R ((fallingSeries R α).subst w) =
      PowerSeries.C α * d⁄dX R w * (fallingSeries R α).subst w := by
  have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw
  have h := congrArg (substAlgHom (R := R) hs)
    (one_add_X_mul_derivative_fallingSeries R α)
  simp only [map_mul, map_add, map_one, coe_substAlgHom, subst_X hs, subst_C] at h
  calc
    (1 + w) * d⁄dX R ((fallingSeries R α).subst w) =
        ((1 + w) * (d⁄dX R (fallingSeries R α)).subst w) * d⁄dX R w := by
      rw [derivative_subst R hs, mul_assoc]
    _ = (PowerSeries.C α * (fallingSeries R α).subst w) * d⁄dX R w := by rw [h]
    _ = _ := by ring

/-- Every normalized formal power has constant coefficient one. -/
theorem coeff_fallingSeries_subst_zero
    {w : R⟦X⟧} (hw : constantCoeff w = 0) (α : R) :
    coeff 0 ((fallingSeries R α).subst w) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply,
    constantCoeff_subst_of_constantCoeff_eq_zero R hw, constantCoeff_fallingSeries]

/-- The coefficient recurrence for `(1+w)^α`, with the factor `n` retained.
The finite sum is exactly `1 ≤ j ≤ n`; the formula also holds at `n = 0`,
where both sides vanish. -/
theorem coeff_fallingSeries_subst_recurrence
    {w : R⟦X⟧} (hw : constantCoeff w = 0) (α : R) (n : ℕ) :
    (n : R) * coeff n ((fallingSeries R α).subst w) =
      ∑ j ∈ Icc 1 n,
        (((α + 1) * (j : R)) - (n : R)) * coeff j w *
          coeff (n - j) ((fallingSeries R α).subst w) := by
  have hderiv : (1 + w) * d⁄dX R ((fallingSeries R α).subst w) =
      PowerSeries.C α * d⁄dX R (1 + w) * (fallingSeries R α).subst w := by
    simpa only [map_add, Derivation.map_one_eq_zero, zero_add] using
      one_add_mul_derivative_fallingSeries_subst R hw α
  have h := natCast_mul_coeff_of_mul_derivative_eq
    (1 + w) ((fallingSeries R α).subst w) α hderiv n
  have hzero : constantCoeff (1 + w) = 1 := by
    rw [map_add, map_one, hw, add_zero]
  rw [hzero, mul_one] at h
  calc
    (n : R) * coeff n ((fallingSeries R α).subst w) =
        ∑ j ∈ Icc 1 n,
          (((α + 1) * (j : R)) - (n : R)) * coeff j (1 + w) *
            coeff (n - j) ((fallingSeries R α).subst w) := h
    _ = _ := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [map_add, coeff_one, if_neg (Nat.ne_of_gt (mem_Icc.mp hj).1), zero_add]

/-- The divided positive-degree recurrence for an arbitrary formal power.
The scalar `1/n` is formed in `ℚ` and mapped to the coefficient algebra;
the coefficient ring itself need not be a field. -/
theorem coeff_fallingSeries_subst_recurrence_of_pos
    {w : R⟦X⟧} (hw : constantCoeff w = 0) (α : R) (n : ℕ) (hn : 1 ≤ n) :
    coeff n ((fallingSeries R α).subst w) =
      algebraMap ℚ R (1 / (n : ℚ)) *
        ∑ j ∈ Icc 1 n,
          (((α + 1) * (j : R)) - (n : R)) * coeff j w *
            coeff (n - j) ((fallingSeries R α).subst w) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hinv : algebraMap ℚ R (1 / (n : ℚ)) * (n : R) = 1 := by
    rw [show (n : R) = algebraMap ℚ R (n : ℚ) by simp,
      ← map_mul, one_div_mul_cancel hnq, map_one]
  calc
    coeff n ((fallingSeries R α).subst w) =
        algebraMap ℚ R (1 / (n : ℚ)) *
          ((n : R) * coeff n ((fallingSeries R α).subst w)) := by
      rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [coeff_fallingSeries_subst_recurrence R hw α n]

end FormalPowers

end Fabius
