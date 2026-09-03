import FabiusFunction.OrdinaryBellComposition
import FabiusFunction.BellHomogeneity
import FabiusFunction.CoefficientRules
import Mathlib.RingTheory.PowerSeries.Log

/-!
# The formal exponential inverts the formal logarithm

Mathlib has `PowerSeries.exp`, `PowerSeries.log` and `PowerSeries.logOf`, but not the fact
that makes them a pair:

`exp(log f) = f`   for `f` with constant term `1`   (`exp_subst_logOf`).

Several results in this corpus want it — the elementary symmetric functions through the
complete Bell polynomials, the cumulant-from-moment formula, and anything else whose source
proof begins "take logarithms" — and each of them would otherwise have to route around it.

The proof is the differential equation, not a coefficient computation.  Write
`W = (1+w)^{-1}|_{w = f-1} · f'`, which is `f'/f` written without an inverse: the geometric
series of `-1` substituted at `f - 1` is a genuine power series, and multiplying it by `f`
gives `1` (`one_add_mul_subst_geomSeries`).  Then the chain rule gives `(log f)' = W`, hence
`(exp(log f))' = exp(log f) · W`, while `f' = f · W`.  Both sides therefore satisfy
`F' = F · W`, they agree at the constant term, and a series with zero constant term
satisfying that equation is zero (`Fabius.eq_zero_of_derivative_eq_mul`).

No inverse is ever formed and no summation over `k` is needed, which is why this works over
an arbitrary commutative `ℚ`-algebra rather than only over a field.

## Main results

* `derivative_log_eq_geomSeries`, `one_add_mul_subst_geomSeries`.
* `constantCoeff_subst_eq`, `derivative_logOf`.
* `exp_subst_logOf`.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

section ExpLog

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `d/dX log(1+X) = ∑_n (-1)^n X^n`, the geometric series of `-1`. -/
theorem derivative_log_eq_geomSeries : d⁄dX A (log A) = geomSeries (-1 : A) := by
  rw [PowerSeries.deriv_log]
  refine PowerSeries.ext fun n => ?_
  rw [coeff_mk, coeff_geomSeries, map_pow, map_neg, map_one]

/-- `(1+X) ∑_n (-1)^n X^n = 1`. -/
theorem one_add_X_mul_geomSeries : ((1 : A⟦X⟧) + X) * geomSeries (-1 : A) = 1 := by
  have h := one_sub_C_mul_X_mul_geomSeries (-1 : A)
  rwa [map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add] at h

/-- The same after substituting any series without constant term: `(1+g)·(1+g)^{-1} = 1`,
with the inverse written as a substituted geometric series. -/
theorem one_add_mul_subst_geomSeries {g : A⟦X⟧} (hg : HasSubst g) :
    (1 + g) * (geomSeries (-1 : A)).subst g = 1 := by
  have h2 := congrArg (substAlgHom (R := A) hg) (one_add_X_mul_geomSeries A)
  rw [map_mul, map_one, map_add, map_one, coe_substAlgHom, subst_X hg] at h2
  exact h2

/-- Substitution of a series without constant term does not move the constant term. -/
theorem constantCoeff_subst_eq (g : A⟦X⟧) {h : A⟦X⟧} (hh : constantCoeff h = 0) :
    constantCoeff (g.subst h) = constantCoeff g := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst_eq_sum_ordPartialBell g hh 0,
    Finset.sum_range_one, ordPartialBell_zero_right, if_pos rfl, mul_one,
    coeff_zero_eq_constantCoeff]

variable {A}

/-- `f - 1` may be substituted whenever `f` has constant term `1`. -/
theorem hasSubst_sub_one {f : A⟦X⟧} (hf : constantCoeff f = 1) : HasSubst (f - 1) :=
  HasSubst.of_constantCoeff_zero' (by rw [map_sub, hf, map_one, sub_self])

/-- **The logarithmic derivative:** `(log f)' = f'/f`, with the quotient written as a
substituted geometric series. -/
theorem derivative_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    d⁄dX A (logOf f) = (geomSeries (-1 : A)).subst (f - 1) * d⁄dX A f := by
  rw [logOf_eq, derivative_subst A (hasSubst_sub_one hf), derivative_log_eq_geomSeries,
    map_sub,
    Derivation.map_one_eq_zero, sub_zero]

/-- `f` times the substituted geometric series is `1`. -/
theorem mul_subst_geomSeries {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f * (geomSeries (-1 : A)).subst (f - 1) = 1 := by
  have h := one_add_mul_subst_geomSeries A (hasSubst_sub_one hf)
  rwa [show (1 : A⟦X⟧) + (f - 1) = f by ring] at h

/-- **The exponential inverts the logarithm:** `exp(log f) = f` for `f` with constant
term `1`. -/
theorem exp_subst_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    (exp A).subst (logOf f) = f := by
  have hL : HasSubst (logOf f) := HasSubst.of_constantCoeff_zero' (constantCoeff_logOf hf)
  set W := (geomSeries (-1 : A)).subst (f - 1) * d⁄dX A f with hW
  have hG : d⁄dX A ((exp A).subst (logOf f)) = (exp A).subst (logOf f) * W := by
    rw [derivative_subst A hL, PowerSeries.derivative_exp, derivative_logOf hf, hW]
  have hfW : d⁄dX A f = f * W := by
    have h1 := mul_subst_geomSeries hf
    calc d⁄dX A f = (f * (geomSeries (-1 : A)).subst (f - 1)) * d⁄dX A f := by
          rw [h1, one_mul]
      _ = f * W := by rw [hW]; ring
  have hD : d⁄dX A ((exp A).subst (logOf f) - f) = ((exp A).subst (logOf f) - f) * W := by
    rw [map_sub, hG, hfW, sub_mul]
  have h0 : constantCoeff ((exp A).subst (logOf f) - f) = 0 := by
    rw [map_sub, constantCoeff_subst_eq A (exp A) (constantCoeff_logOf hf), constantCoeff_exp,
      hf, sub_self]
  have hz := eq_zero_of_derivative_eq_mul (A := A) hD h0
  rwa [sub_eq_zero] at hz

end ExpLog

end Fabius
