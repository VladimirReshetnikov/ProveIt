import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Coefficient rules for formal power series

The three elementary coefficient rules used throughout the coefficient calculus, over an arbitrary
commutative ring:

* the Cauchy product `[z^n] F G = ∑_{j ≤ n} f_j g_{n-j}` (`coeff_mul_eq_sum_range`),
* differentiation `[z^n] F' = (n+1) f_{n+1}` (`coeff_derivative_eq`),
* the geometric convolution `[z^n] F/(1-az) = ∑_{j ≤ n} a^{n-j} f_j` (`coeff_mul_geomSeries`).

The geometric series `∑_n a^n z^n` is `geomSeries a`; it is the two-sided inverse of `1 - a z`
(`one_sub_C_mul_X_mul_geomSeries`, `isUnit_one_sub_C_mul_X`), which is the form in which the third
rule is stated: `F/(1-az)` is `F * geomSeries a`, and `G = F * geomSeries a` is characterised by
`(1 - a z) G = F` (`eq_mul_geomSeries_iff`).

## Main results

* `geomSeries`, `coeff_geomSeries`, `one_sub_C_mul_X_mul_geomSeries`, `isUnit_one_sub_C_mul_X`,
  `eq_mul_geomSeries_iff`.
* `coeff_mul_eq_sum_range`, `coeff_derivative_eq`, `coeff_mul_geomSeries`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

variable {R : Type*} [CommRing R]

/-- The geometric series `∑_n a^n z^n`. -/
noncomputable def geomSeries (a : R) : R⟦X⟧ := PowerSeries.mk fun n => a ^ n

@[simp] theorem coeff_geomSeries (a : R) (n : ℕ) :
    coeff n (geomSeries a) = a ^ n := coeff_mk _ _

/-- `(1 - az) ∑_n a^n z^n = 1`. -/
theorem one_sub_C_mul_X_mul_geomSeries (a : R) :
    (1 - PowerSeries.C a * X) * geomSeries a = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_geomSeries, mul_assoc, coeff_C_mul, coeff_one]
  cases n with
  | zero => rw [coeff_zero_X_mul, pow_zero, mul_zero, sub_zero, if_pos rfl]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_geomSeries, if_neg (Nat.succ_ne_zero n), pow_succ]
    ring

/-- `1 - az` is a unit of `R⟦z⟧`, with inverse the geometric series. -/
theorem isUnit_one_sub_C_mul_X (a : R) : IsUnit (1 - PowerSeries.C a * X : R⟦X⟧) :=
  IsUnit.of_mul_eq_one _ (one_sub_C_mul_X_mul_geomSeries a)

/-- `G = F/(1-az)` exactly when `(1-az) G = F`. -/
theorem eq_mul_geomSeries_iff (a : R) (F G : R⟦X⟧) :
    G = F * geomSeries a ↔ (1 - PowerSeries.C a * X) * G = F := by
  constructor
  · rintro rfl
    rw [← mul_assoc, mul_comm _ F, mul_assoc, one_sub_C_mul_X_mul_geomSeries, mul_one]
  · rintro rfl
    have h : (1 - PowerSeries.C a * X) * G * geomSeries a =
        ((1 - PowerSeries.C a * X) * geomSeries a) * G := by ring
    rw [h, one_sub_C_mul_X_mul_geomSeries, one_mul]

/-- **The Cauchy product rule:** `[z^n] F G = ∑_{j ≤ n} f_j g_{n-j}`. -/
theorem coeff_mul_eq_sum_range (F G : R⟦X⟧) (n : ℕ) :
    coeff n (F * G) = ∑ j ∈ range (n + 1), coeff j F * coeff (n - j) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- **The derivative rule:** `[z^n] F' = (n+1) f_{n+1}`. -/
theorem coeff_derivative_eq (F : R⟦X⟧) (n : ℕ) :
    coeff n (d⁄dX R F) = ((n : R) + 1) * coeff (n + 1) F := by
  rw [coeff_derivative, mul_comm]

/-- **The geometric convolution rule:** `[z^n] F/(1-az) = ∑_{j ≤ n} a^{n-j} f_j`. -/
theorem coeff_mul_geomSeries (a : R) (F : R⟦X⟧) (n : ℕ) :
    coeff n (F * geomSeries a) = ∑ j ∈ range (n + 1), a ^ (n - j) * coeff j F := by
  rw [coeff_mul_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => by rw [coeff_geomSeries, mul_comm]

/-- The same rule for a series presented by its defining equation `(1-az) G = F`. -/
theorem coeff_eq_sum_of_one_sub_C_mul_X_mul_eq (a : R) {F G : R⟦X⟧}
    (h : (1 - PowerSeries.C a * X) * G = F) (n : ℕ) :
    coeff n G = ∑ j ∈ range (n + 1), a ^ (n - j) * coeff j F := by
  rw [(eq_mul_geomSeries_iff a F G).mpr h, coeff_mul_geomSeries]

end Fabius
