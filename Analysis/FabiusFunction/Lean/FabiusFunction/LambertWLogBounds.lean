import FabiusFunction.PrincipalLambertWAtTop

/-!
# Logarithmic bounds for the principal Lambert branch at large arguments

For `x > e`, writing `L = log x > 1`, the Lambert W guide's "logarithmic
bounds for large positive arguments" read

`L - log L < W₀(x) < L - log (L - log L) < L`.

`PrincipalLambertWAtTop` already proves the outer bracket
`L - log L ≤ W₀(x) ≤ L` for `x ≥ e`.  This module adds the sharper upper
bound and the strict forms.

## The mechanism

Everything comes from the identity `W + log W = L` (`principalLambertW_add_log`)
and monotonicity of the logarithm: since `W ≥ L - log L > 0`,

`W = L - log W ≤ L - log (L - log L)`,

and for `x > e` the inequalities are strict because `W > 1` makes `log W > 0`,
so `W < L` strictly, hence `L - log L < W` strictly, hence the rest.  This is
one more turn of the same crank that produces the asymptotic expansion
`W = L - log L + (log L)/L + ⋯`; each turn substitutes the previous bracket
into `log W`.
-/

set_option autoImplicit false

namespace Fabius

/-- On `x ≥ e`, `L - log L > 0` where `L = log x`. -/
theorem log_sub_log_log_pos_of_exp_one_le {x : ℝ} (hx : Real.exp 1 ≤ x) :
    0 < Real.log x - Real.log (Real.log x) := by
  have hL : 1 ≤ Real.log x := one_le_log_of_exp_one_le hx
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log x)
  linarith

/-- **The sharper upper bound.**  For `x ≥ e` and `L = log x`,
`W₀(x) ≤ L - log (L - log L)`. -/
theorem principalLambertW_le_log_sub_log_log_sub_log_log {x : ℝ} (hx : Real.exp 1 ≤ x) :
    principalLambertW x ≤ Real.log x - Real.log (Real.log x - Real.log (Real.log x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hid := principalLambertW_add_log hx0
  have hlow := log_sub_log_log_le_principalLambertW hx
  have hpos := log_sub_log_log_pos_of_exp_one_le hx
  have := Real.log_le_log hpos hlow
  linarith

/-- For `x > e`, `W₀(x) < log x` strictly: `log W₀(x) > 0`. -/
theorem principalLambertW_lt_log {x : ℝ} (hx : Real.exp 1 < x) :
    principalLambertW x < Real.log x := by
  have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
  have hid := principalLambertW_add_log hx0
  have hW : 1 < principalLambertW x := by
    have he : -Real.exp (-1) ≤ Real.exp 1 := by linarith [Real.exp_pos (-1), Real.exp_pos 1]
    have hxm : -Real.exp (-1) ≤ x := by linarith [Real.exp_pos (-1)]
    rw [← principalLambertW_exp_one]
    exact principalLambertW_strictMonoOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr hxm) hx
  have := Real.log_pos hW
  linarith

/-- For `x > e`, `L - log L < W₀(x)` strictly. -/
theorem log_sub_log_log_lt_principalLambertW {x : ℝ} (hx : Real.exp 1 < x) :
    Real.log x - Real.log (Real.log x) < principalLambertW x := by
  have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
  have hid := principalLambertW_add_log hx0
  have hW : 0 < principalLambertW x := principalLambertW_pos hx0
  have := Real.log_lt_log hW (principalLambertW_lt_log hx)
  linarith

/-- For `x > e`, `W₀(x) < L - log (L - log L)` strictly. -/
theorem principalLambertW_lt_log_sub_log_log_sub_log_log {x : ℝ} (hx : Real.exp 1 < x) :
    principalLambertW x < Real.log x - Real.log (Real.log x - Real.log (Real.log x)) := by
  have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
  have hid := principalLambertW_add_log hx0
  have hpos := log_sub_log_log_pos_of_exp_one_le hx.le
  have := Real.log_lt_log hpos (log_sub_log_log_lt_principalLambertW hx)
  linarith

/-- **The guide's chain**, for `x > e` and `L = log x`:
`L - log L < W₀(x) < L - log (L - log L) < L`. -/
theorem principalLambertW_log_bounds {x : ℝ} (hx : Real.exp 1 < x) :
    Real.log x - Real.log (Real.log x) < principalLambertW x ∧
      principalLambertW x < Real.log x - Real.log (Real.log x - Real.log (Real.log x)) ∧
      Real.log x - Real.log (Real.log x - Real.log (Real.log x)) < Real.log x := by
  refine ⟨log_sub_log_log_lt_principalLambertW hx,
    principalLambertW_lt_log_sub_log_log_sub_log_log hx, ?_⟩
  have hpos := log_sub_log_log_pos_of_exp_one_le hx.le
  -- `log (L - log L) > 0` because `L - log L > 1`: `log L < L - 1` for `L > 1`
  have hL : 1 < Real.log x := by
    have := Real.log_lt_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hgt : 1 < Real.log x - Real.log (Real.log x) := by
    have := Real.log_lt_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log x) hL.ne'
    linarith
  linarith [Real.log_pos hgt]

end Fabius
