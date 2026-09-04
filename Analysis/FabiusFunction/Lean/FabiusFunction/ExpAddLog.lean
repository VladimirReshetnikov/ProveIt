import FabiusFunction.ExpLog
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The exponential law, and the logarithm as its inverse

`ExpLog` supplies `exp(log f) = f`.  This module supplies the rest of the pair:

`exp(g + h) = exp(g) · exp(h)`   (`exp_subst_add`),
`log(exp g) = g`   (`logOf_exp_subst`),
`log(f · g) = log f + log g`   (`logOf_mul`),

for formal power series over an arbitrary commutative `ℚ`-algebra, with `g`, `h` of zero
constant term and `f`, `g` of constant term `1`.  Together these say that `exp` is an
isomorphism from the additive group of series with zero constant term onto the multiplicative
group of series with constant term `1`, with `log` as its inverse.

Every proof here is the differential-equation argument of `ExpLog`, which is what keeps them
at the generality of a commutative `ℚ`-algebra: the two sides satisfy `F' = F · W` for the
same `W`, agree at the constant term, and `Fabius.eq_zero_of_derivative_eq_mul` finishes.
Injectivity needs one extra fact, that a series with zero derivative and zero constant term is
zero (`eq_zero_of_derivative_eq_zero`), which over a `ℚ`-algebra is the invertibility of
`n+1` and nothing more.

## Main results

* `eq_zero_of_derivative_eq_zero`, `constantCoeff_exp_subst`.
* `exp_subst_add`, `eq_zero_of_exp_subst_eq_one`, `exp_subst_injective`.
* `logOf_exp_subst`, `logOf_mul`.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

section ExpAdd

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- A series with zero derivative and zero constant term is zero. -/
theorem eq_zero_of_derivative_eq_zero {c : A⟦X⟧} (hc : d⁄dX A c = 0)
    (h0 : constantCoeff c = 0) : c = 0 := by
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero => rw [coeff_zero_eq_constantCoeff, h0, map_zero]
  | succ m =>
    have hm : coeff m (d⁄dX A c) = 0 := by rw [hc, map_zero]
    rw [coeff_derivative] at hm
    have hcast : algebraMap ℚ A ((m : ℚ) + 1) = (m : A) + 1 := by
      rw [map_add, map_natCast, map_one]
    have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
    have hinv : ((m : A) + 1) * algebraMap ℚ A (1 / ((m : ℚ) + 1)) = 1 := by
      rw [← hcast, ← map_mul, mul_one_div_cancel hne, map_one]
    calc coeff (m + 1) c
        = coeff (m + 1) c * (((m : A) + 1) * algebraMap ℚ A (1 / ((m : ℚ) + 1))) := by
          rw [hinv, mul_one]
      _ = (coeff (m + 1) c * ((m : A) + 1)) * algebraMap ℚ A (1 / ((m : ℚ) + 1)) := by ring
      _ = 0 := by rw [hm, zero_mul]
      _ = coeff (m + 1) (0 : A⟦X⟧) := by rw [map_zero]

variable {A}

/-- `exp(g)` has constant term `1`. -/
theorem constantCoeff_exp_subst {g : A⟦X⟧} (hg : constantCoeff g = 0) :
    constantCoeff ((exp A).subst g) = 1 := by
  rw [constantCoeff_subst_eq A (exp A) hg, constantCoeff_exp]

/-- **The exponential law:** `exp(g + h) = exp(g) · exp(h)`. -/
theorem exp_subst_add {g h : A⟦X⟧} (hg : constantCoeff g = 0) (hh : constantCoeff h = 0) :
    (exp A).subst (g + h) = (exp A).subst g * (exp A).subst h := by
  have hgh : constantCoeff (g + h) = 0 := by rw [map_add, hg, hh, add_zero]
  have hsg : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have hsh : HasSubst h := HasSubst.of_constantCoeff_zero' hh
  have hsgh : HasSubst (g + h) := HasSubst.of_constantCoeff_zero' hgh
  set W := d⁄dX A g + d⁄dX A h with hW
  have hL : d⁄dX A ((exp A).subst (g + h)) = (exp A).subst (g + h) * W := by
    rw [derivative_subst A hsgh, PowerSeries.derivative_exp, map_add, hW]
  have hR : d⁄dX A ((exp A).subst g * (exp A).subst h) =
      (exp A).subst g * (exp A).subst h * W := by
    rw [Derivation.leibniz, derivative_subst A hsg, derivative_subst A hsh,
      PowerSeries.derivative_exp, smul_eq_mul, smul_eq_mul, hW]
    ring
  have hD : d⁄dX A ((exp A).subst (g + h) - (exp A).subst g * (exp A).subst h) =
      ((exp A).subst (g + h) - (exp A).subst g * (exp A).subst h) * W := by
    rw [map_sub, hL, hR, sub_mul]
  have h0 : constantCoeff ((exp A).subst (g + h) - (exp A).subst g * (exp A).subst h) = 0 := by
    rw [map_sub, map_mul, constantCoeff_exp_subst hgh, constantCoeff_exp_subst hg,
      constantCoeff_exp_subst hh, one_mul, sub_self]
  have hz := eq_zero_of_derivative_eq_mul (A := A) hD h0
  rwa [sub_eq_zero] at hz

/-- `exp(c) = 1` forces `c = 0`. -/
theorem eq_zero_of_exp_subst_eq_one {c : A⟦X⟧} (hc : constantCoeff c = 0)
    (h1 : (exp A).subst c = 1) : c = 0 := by
  have hs : HasSubst c := HasSubst.of_constantCoeff_zero' hc
  have hd : d⁄dX A c = 0 := by
    have h := congrArg (d⁄dX A) h1
    rw [derivative_subst A hs, PowerSeries.derivative_exp, h1, one_mul,
      Derivation.map_one_eq_zero] at h
    exact h
  exact eq_zero_of_derivative_eq_zero A hd hc

/-- `exp` is injective on series with zero constant term. -/
theorem exp_subst_injective {g h : A⟦X⟧} (hg : constantCoeff g = 0) (hh : constantCoeff h = 0)
    (hgh : (exp A).subst g = (exp A).subst h) : g = h := by
  have hd : constantCoeff (g - h) = 0 := by rw [map_sub, hg, hh, sub_self]
  have hmul : (exp A).subst (g - h) * (exp A).subst h = (exp A).subst h := by
    rw [← exp_subst_add hd hh, sub_add_cancel, hgh]
  have hu : IsUnit ((exp A).subst h) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_exp_subst hh]
    exact isUnit_one
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hone : (exp A).subst (g - h) = 1 := by
    calc (exp A).subst (g - h)
        = (exp A).subst (g - h) * ((exp A).subst h * v) := by rw [hv, mul_one]
      _ = ((exp A).subst (g - h) * (exp A).subst h) * v := by ring
      _ = (exp A).subst h * v := by rw [hmul]
      _ = 1 := hv
  have hz := eq_zero_of_exp_subst_eq_one hd hone
  rwa [sub_eq_zero] at hz

/-- **The logarithm inverts the exponential:** `log(exp g) = g`. -/
theorem logOf_exp_subst {g : A⟦X⟧} (hg : constantCoeff g = 0) :
    logOf ((exp A).subst g) = g := by
  have hE : constantCoeff ((exp A).subst g) = 1 := constantCoeff_exp_subst hg
  refine exp_subst_injective (constantCoeff_logOf hE) hg ?_
  rw [exp_subst_logOf hE]

/-- **The logarithm turns products into sums.** -/
theorem logOf_mul {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, one_mul]
  have hsum : constantCoeff (logOf f + logOf g) = 0 := by
    rw [map_add, constantCoeff_logOf hf, constantCoeff_logOf hg, add_zero]
  refine exp_subst_injective (constantCoeff_logOf hfg) hsum ?_
  rw [exp_subst_logOf hfg, exp_subst_add (constantCoeff_logOf hf) (constantCoeff_logOf hg),
    exp_subst_logOf hf, exp_subst_logOf hg]

end ExpAdd

end Fabius
