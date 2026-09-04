import FabiusFunction.BellPolynomialMoments
import FabiusFunction.ExpAddLog
import FabiusFunction.SaddleLogExpansionPowerSeries

/-!
# The formal logarithm of the Bernoulli kernel

For `B(t) = t/(exp(t)-1)`, normalized by `B(0)=1`, this module proves

`log B(t) = -t/2 - ∑_{n ≥ 2} bernoulli n * t^n / (n * n!)`.

The logarithm is Mathlib's `PowerSeries.logOf`, defined by substitution into
the universal formal logarithm.  Its coefficients are derived from the
already-proved logarithm of the reciprocal kernel `(exp(t)-1)/t`.
The existing `SaddleExpansion.logSeries_eq_logOf` identifies that coefficient
recurrence with Mathlib's logarithm; the logarithm product law supplies the
minus sign.

The distinction between the two Bernoulli conventions matters in degree one.
The formula valid in every positive degree uses `bernoulli'`, whose first
value is `1/2`.  The ordinary numbers `bernoulli`, with first value `-1/2`,
give the displayed formula only from degree two onward.  Degree zero is
explicitly zero.

These are identities of formal power series over `ℚ`.  No convergence radius
or identification with an analytic logarithm is asserted here.

## Main declarations

* `bernoulliPowerSeries_mul_massSeries_expm1Div`: the two kernels are inverses.
* `logOf_bernoulliPowerSeries`: the exact formal logarithm series.
* `coeff_logOf_bernoulliPowerSeries`: the all-index formula, with a separate
  zero case and the positive Bernoulli convention.
* `coeff_one_logOf_bernoulliPowerSeries`: the linear coefficient is `-1/2`.
* `coeff_logOf_bernoulliPowerSeries_of_two_le`: the ordinary-Bernoulli form
  in every degree at least two.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- The Bernoulli kernel `t/(exp(t)-1)` and the explicitly constructed
series `(exp(t)-1)/t` multiply to one. -/
theorem bernoulliPowerSeries_mul_massSeries_expm1Div :
    bernoulliPowerSeries ℚ * SaddleExpansion.massSeries expm1DivCoefficient = 1 := by
  apply mul_left_cancel₀ (show (X : ℚ⟦X⟧) ≠ 0 from X_ne_zero)
  calc
    X * (bernoulliPowerSeries ℚ * SaddleExpansion.massSeries expm1DivCoefficient) =
        bernoulliPowerSeries ℚ * (X * SaddleExpansion.massSeries expm1DivCoefficient) := by
      ring
    _ = bernoulliPowerSeries ℚ * (exp ℚ - 1) := by rw [X_mul_massSeries_expm1Div]
    _ = X := bernoulliPowerSeries_mul_exp_sub_one ℚ
    _ = X * 1 := (mul_one X).symm

/-- The logarithm of the Bernoulli kernel is the negative of the known
Bernoulli logarithm of its reciprocal.  This is an identity of formal
series, not an assumed coefficient expansion. -/
theorem logOf_bernoulliPowerSeries :
    PowerSeries.logOf (bernoulliPowerSeries ℚ) = -PowerSeries.mk bernoulliLogCoefficient := by
  have hB : constantCoeff (bernoulliPowerSeries ℚ) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, bernoulliPowerSeries, coeff_mk]
    simp
  have hG : constantCoeff (SaddleExpansion.massSeries expm1DivCoefficient) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, SaddleExpansion.coeff_massSeries,
      expm1DivCoefficient_zero]
  have hGlog :
      PowerSeries.logOf (SaddleExpansion.massSeries expm1DivCoefficient) =
        PowerSeries.mk bernoulliLogCoefficient := by
    ext n
    rw [← SaddleExpansion.logSeries_eq_logOf expm1DivCoefficient expm1DivCoefficient_zero,
      SaddleExpansion.coeff_logSeries, coeff_mk, expm1Div_logCoeff_eq_bernoulli]
  have hsum : PowerSeries.logOf (bernoulliPowerSeries ℚ) +
      PowerSeries.logOf (SaddleExpansion.massSeries expm1DivCoefficient) = 0 := by
    rw [← Fabius.logOf_mul hB hG, bernoulliPowerSeries_mul_massSeries_expm1Div,
      PowerSeries.logOf_eq, sub_self, subst_zero_of_constantCoeff_zero constantCoeff_log]
  rw [hGlog] at hsum
  calc
    PowerSeries.logOf (bernoulliPowerSeries ℚ) =
        (PowerSeries.logOf (bernoulliPowerSeries ℚ) + PowerSeries.mk bernoulliLogCoefficient) -
          PowerSeries.mk bernoulliLogCoefficient := (add_sub_cancel_right _ _).symm
    _ = -PowerSeries.mk bernoulliLogCoefficient := by rw [hsum, zero_sub]

/-- Every coefficient of the normalized formal logarithm of the Bernoulli
kernel.  Positive degrees use `bernoulli'`, whose first value is `1/2`;
the constant coefficient is zero. -/
theorem coeff_logOf_bernoulliPowerSeries (n : ℕ) :
    coeff n (PowerSeries.logOf (bernoulliPowerSeries ℚ)) =
      if n = 0 then 0 else -(bernoulli' n / ((n : ℚ) * n.factorial)) := by
  rw [logOf_bernoulliPowerSeries, map_neg, coeff_mk, bernoulliLogCoefficient]
  split_ifs <;> simp only [neg_zero]

/-- The linear coefficient of `log(t/(exp(t)-1))` is `-1/2`. -/
theorem coeff_one_logOf_bernoulliPowerSeries :
    coeff 1 (PowerSeries.logOf (bernoulliPowerSeries ℚ)) = -(1 / 2 : ℚ) := by
  rw [coeff_logOf_bernoulliPowerSeries]
  norm_num [bernoulli'_one]

/-- From degree two onward the coefficient uses the ordinary Bernoulli
numbers: `[t^n] log(t/(exp(t)-1)) = -B_n/(n*n!)`. -/
theorem coeff_logOf_bernoulliPowerSeries_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    coeff n (PowerSeries.logOf (bernoulliPowerSeries ℚ)) =
      -(bernoulli n / ((n : ℚ) * n.factorial)) := by
  rw [coeff_logOf_bernoulliPowerSeries, if_neg (by omega),
    ← bernoulli_eq_bernoulli'_of_ne_one (by omega : n ≠ 1)]

end Fabius
