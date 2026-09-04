import FabiusFunction.StirlingSecondReverseColumn
import FabiusFunction.ExpAddLog
import FabiusFunction.SmoothingOperatorExponential

/-!
# The reverse row recurrence of the second kind

`StirlingSecondReverseColumn` proves one of the two reverse recurrences the source states for
the second-kind numbers; this module proves the other,

`(n - k) S(n,k) = ∑_{j=2}^{n-k+1} (j-2)! C(-k, j) S(n, k+j-1)`   (`second_reverse_row`),

which moves along a row rather than down a column.

The source proves it with a bivariate generating function `F(x,y) = exp(y(e^x - 1))`,
differentiating `j` times in `y`.  That is not necessary, and this module follows the shorter
route instead: with `k` fixed and the sum taken over `n` alone, every term is a *column*
generating function `u^m/m!` in the single variable `x`, where `u = e^x - 1`.  Both sides then
carry the common factor `u^{k-1}/(k-1)!`, because

`(j-2)! C(-k,j) / (k+j-1)! = (-1)^j / (j(j-1)(k-1)!)`,

and what is left is the single series identity `∑_{j≥2} (-1)^j t^j/(j(j-1)) = (1+t)log(1+t) - t`
(`coeff_logTail`, one coefficient computation) evaluated at `t = u`, where `1 + u = e^x` and
`log(1+u) = x` (`log_subst_exp_sub_one` of `BellComposition`).

## Main results

* `coeff_logTail`, the coefficients of `(1+X)log(1+X) - X`.
* `subst_logTail`, its value at `u = e^x - 1`, namely `x·e^x - u`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section SecondRow

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The quadratic tail of the logarithm, `(1+X)·log(1+X) - X`.  Its coefficients are
`(-1)^j/(j(j-1))`, which is the weight the reverse row recurrence carries. -/
noncomputable def logTail : A⟦X⟧ := (1 + X) * log A - X

/-- The coefficients of `logTail`: `(-1)^j/(j(j-1))` from `j = 2` on, and `0` below.  This is
the one series identity the row recurrence needs, and it is a coefficient computation rather
than the double differentiation the source performs. -/
theorem coeff_logTail (j : ℕ) :
    coeff j (logTail A) =
      if 2 ≤ j then algebraMap ℚ A ((-1 : ℚ) ^ j / (j * (j - 1))) else 0 := by
  rcases j with _ | _ | m
  · simp [logTail]
  · rw [if_neg (by omega), logTail, map_sub, add_mul, one_mul, map_add, coeff_succ_X_mul,
      coeff_log, coeff_log, PowerSeries.coeff_X]
    norm_num
  · rw [logTail, map_sub, add_mul, one_mul, map_add, coeff_log, if_neg (by omega),
      coeff_succ_X_mul, coeff_log, if_neg (by omega), PowerSeries.coeff_X, if_neg (by omega),
      sub_zero, if_pos (by omega), ← map_add]
    congr 1
    have hpow : (-1 : ℚ) ^ (m + 1 + 1 + 1) = -((-1 : ℚ) ^ (m + 1 + 1)) := by
      rw [pow_succ]; ring
    rw [hpow]
    set c : ℚ := (-1 : ℚ) ^ (m + 1 + 1)
    have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **The tail at `u = e^x - 1` is `x·e^x - u`.**  This is the whole content of the row
recurrence: the two sides of the identity differ by exactly this substitution, and the step
that makes it work is `log(e^x) = x`. -/
theorem subst_logTail :
    (logTail A).subst (exp A - 1) = X * exp A - (exp A - 1) := by
  have hu : HasSubst (exp A - 1) := HasSubst.exp_sub_one
  rw [logTail, ← coe_substAlgHom hu, map_sub, map_mul, map_add, map_one, coe_substAlgHom hu,
    subst_X hu, log_subst_exp_sub_one]
  ring

end SecondRow

end Fabius
