import FabiusFunction.ExpAddLog
import FabiusFunction.CatalanGeneratingFunction

/-!
# Square roots of power series, and the Catalan closed form

A formal power series with constant term `1` has a unique square root with constant term `1`,

`sqrtOf f = exp(½ log f)`,   `(sqrtOf f)² = f`   (`sq_sqrtOf`),

over any commutative `ℚ`-algebra.  Existence is the exponential law of `ExpAddLog`; uniqueness
is elementary, because two such roots `u`, `v` satisfy `(u-v)(u+v) = 0` and `u+v` has constant
term `2`, which is a unit (`sqrt_unique`).

The payoff recorded here is the closed form the source states for the Catalan generating
function:

`√(1 - 4z) = 1 - 2z C(z)`   (`sqrtOf_one_sub_four_X`),

which was the one part of that theorem the corpus did not carry.  The proof needs no
analysis and no binomial series: squaring `1 - 2zC` and using `zC² = C - 1` gives `1 - 4z`
outright, and uniqueness does the rest.

Note what the statement is *not*.  It is not a claim about a real or complex square root; it
is an identity between two formal power series over a `ℚ`-algebra, and the `√` is the one
defined here.  The source's radius of convergence and its branch cut are analytic and remain
unformalized.

## Main results

* `sqrtOf`, `constantCoeff_sqrtOf`, `sq_sqrtOf`, `sqrt_unique`.
* `sq_one_sub_two_X_mul_catalanSeries`, `sqrtOf_one_sub_four_X`.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

section Sqrt

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The constant term of a scaled series. -/
theorem constantCoeff_smul (c : A) (g : A⟦X⟧) :
    constantCoeff (c • g) = c * constantCoeff g := by
  rw [← coeff_zero_eq_constantCoeff, coeff_smul, smul_eq_mul, coeff_zero_eq_constantCoeff]

/-- The square root of a series with constant term `1`, as `exp(½ log f)`. -/
noncomputable def sqrtOf (f : A⟦X⟧) : A⟦X⟧ :=
  (exp A).subst (algebraMap ℚ A (1 / 2) • logOf f)

/-- `√f` has constant term `1`. -/
theorem constantCoeff_sqrtOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    constantCoeff (sqrtOf f) = 1 := by
  refine constantCoeff_exp_subst ?_
  rw [constantCoeff_smul, constantCoeff_logOf hf, mul_zero]

/-- **`√f` squares to `f`.** -/
theorem sq_sqrtOf {f : A⟦X⟧} (hf : constantCoeff f = 1) : sqrtOf f ^ 2 = f := by
  have h0 : constantCoeff (algebraMap ℚ A (1 / 2) • logOf f) = 0 := by
    rw [constantCoeff_smul, constantCoeff_logOf hf, mul_zero]
  have hhalf : algebraMap ℚ A (1 / 2) • logOf f + algebraMap ℚ A (1 / 2) • logOf f
      = logOf f := by
    rw [← add_smul, ← map_add, show (1 : ℚ) / 2 + 1 / 2 = 1 by norm_num, map_one, one_smul]
  calc sqrtOf f ^ 2 = sqrtOf f * sqrtOf f := by ring
    _ = (exp A).subst (algebraMap ℚ A (1 / 2) • logOf f + algebraMap ℚ A (1 / 2) • logOf f) := by
        rw [sqrtOf, exp_subst_add h0 h0]
    _ = f := by rw [hhalf, exp_subst_logOf hf]

/-- **Uniqueness:** a square root with constant term `1` is unique. -/
theorem sqrt_unique {f u v : A⟦X⟧} (hu : u ^ 2 = f) (hv : v ^ 2 = f)
    (hu1 : constantCoeff u = 1) (hv1 : constantCoeff v = 1) : u = v := by
  have hprod : (u - v) * (u + v) = 0 := by
    have : (u - v) * (u + v) = u ^ 2 - v ^ 2 := by ring
    rw [this, hu, hv, sub_self]
  have hunit : IsUnit (u + v) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, hu1, hv1]
    have htwo : algebraMap ℚ A (2 : ℚ) = (1 : A) + 1 := by
      rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
    refine IsUnit.of_mul_eq_one (algebraMap ℚ A (1 / 2)) ?_
    rw [← htwo, ← map_mul, show (2 : ℚ) * (1 / 2) = 1 by norm_num, map_one]
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have : u - v = 0 := by
    calc u - v = (u - v) * ((u + v) * w) := by rw [hw, mul_one]
      _ = ((u - v) * (u + v)) * w := by ring
      _ = 0 := by rw [hprod, zero_mul]
  rwa [sub_eq_zero] at this

end Sqrt

section Catalan

variable (R : Type*) [CommRing R]

/-- Squaring `1 - 2zC` gives `1 - 4z`, using only `C = 1 + zC²`. -/
theorem sq_one_sub_two_X_mul_catalanSeries :
    (1 - 2 * X * catalanSeries R) ^ 2 = 1 - 4 * X := by
  have hC := catalanSeries_eq R
  have hkey : X * catalanSeries R ^ 2 = catalanSeries R - 1 := by
    linear_combination -hC
  calc (1 - 2 * X * catalanSeries R) ^ 2
      = 1 - 4 * (X * catalanSeries R) + 4 * X * (X * catalanSeries R ^ 2) := by ring
    _ = 1 - 4 * (X * catalanSeries R) + 4 * X * (catalanSeries R - 1) := by rw [hkey]
    _ = 1 - 4 * X := by ring

/-- `1 - 2zC` has constant term `1`. -/
theorem constantCoeff_one_sub_two_X_mul_catalanSeries :
    constantCoeff (1 - 2 * X * catalanSeries R) = 1 := by
  rw [map_sub, map_one, map_mul, map_mul, constantCoeff_X, mul_zero, zero_mul, sub_zero]

end Catalan

/-- **The Catalan closed form:** `√(1 - 4z) = 1 - 2z C(z)`, as formal power series. -/
theorem sqrtOf_one_sub_four_X (A : Type*) [CommRing A] [Algebra ℚ A] :
    sqrtOf (1 - 4 * X : A⟦X⟧) = 1 - 2 * X * catalanSeries A := by
  have hf : constantCoeff (1 - 4 * X : A⟦X⟧) = 1 := by
    rw [map_sub, map_one, map_mul, constantCoeff_X, mul_zero, sub_zero]
  refine sqrt_unique (f := (1 - 4 * X : A⟦X⟧)) (sq_sqrtOf hf)
    (sq_one_sub_two_X_mul_catalanSeries A) (constantCoeff_sqrtOf hf)
    (constantCoeff_one_sub_two_X_mul_catalanSeries A)

end Fabius
