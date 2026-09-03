import FabiusFunction.LambertWElementaryBounds
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# The principal Lambert branch at infinity

The defining equation `W(x)·e^(W(x)) = x` of the principal branch,
read through the logarithm, is the **exact functional identity**

`W(x) + log W(x) = log x`   (`x > 0`),

from which the whole asymptotic behaviour of `W₀` at `+∞` follows by
elementary bookkeeping.  Writing `L = log x` and `ℓ = log log x`:

* `principalLambertW_le_log`, `log_sub_log_log_le_principalLambertW` —
  the two-sided bracket `L - ℓ ≤ W(x) ≤ L` for `x ≥ e`;
* `principalLambertW_isEquivalent_log` — `W ~ log` at `+∞`;
* `tendsto_principalLambertW_atTop` — `W(x) → ∞`;
* `tendsto_principalLambertW_sub_log_sub_log_log` — the **two-term
  expansion** `W(x) = L - ℓ + o(1)`: the error `W - (L - ℓ)` tends to
  `0`.

The higher terms `∑ P_n(ℓ)/L^n` of the classical expansion are not
formalized here; the identity `W = L - log W` iterates to them.
-/

set_option autoImplicit false

open Filter Topology Asymptotics Set

namespace Fabius

/-- **The logarithmic form of the defining equation**:
`W(x) + log W(x) = log x` for every `x > 0`. -/
theorem principalLambertW_add_log {x : ℝ} (hx : 0 < x) :
    principalLambertW x + Real.log (principalLambertW x) = Real.log x := by
  have hW := principalLambertW_pos hx
  have h := principalLambertW_mul_exp (z := x)
    (by linarith [Real.exp_pos (-1)])
  conv_rhs => rw [← h]
  rw [Real.log_mul hW.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `W(x) ≥ 1` for `x ≥ e` (monotonicity from `W(e) = 1`). -/
theorem one_le_principalLambertW {x : ℝ} (hx : Real.exp 1 ≤ x) :
    1 ≤ principalLambertW x := by
  rw [← principalLambertW_exp_one]
  have he : -Real.exp (-1) ≤ Real.exp 1 := by
    linarith [Real.exp_pos (-1), Real.exp_pos 1]
  exact principalLambertW_strictMonoOn.monotoneOn he (le_trans he hx) hx

/-- `1 ≤ log x` for `x ≥ e`. -/
theorem one_le_log_of_exp_one_le {x : ℝ} (hx : Real.exp 1 ≤ x) :
    1 ≤ Real.log x := by
  have h := Real.log_le_log (Real.exp_pos 1) hx
  rwa [Real.log_exp] at h

/-- **Upper bound**: `W(x) ≤ log x` for `x ≥ e`. -/
theorem principalLambertW_le_log {x : ℝ} (hx : Real.exp 1 ≤ x) :
    principalLambertW x ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have h := principalLambertW_add_log hx0
  have hlog : 0 ≤ Real.log (principalLambertW x) :=
    Real.log_nonneg (one_le_principalLambertW hx)
  linarith

/-- **Lower bound**: `log x - log log x ≤ W(x)` for `x ≥ e`. -/
theorem log_sub_log_log_le_principalLambertW {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Real.log x - Real.log (Real.log x) ≤ principalLambertW x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have h := principalLambertW_add_log hx0
  have hW := principalLambertW_pos hx0
  have hle : Real.log (principalLambertW x) ≤ Real.log (Real.log x) :=
    Real.log_le_log hW (principalLambertW_le_log hx)
  linarith

/-- The two-sided bracket `log x - log log x ≤ W(x) ≤ log x` for
`x ≥ e`. -/
theorem principalLambertW_log_bracket {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Real.log x - Real.log (Real.log x) ≤ principalLambertW x ∧
      principalLambertW x ≤ Real.log x :=
  ⟨log_sub_log_log_le_principalLambertW hx, principalLambertW_le_log hx⟩

/-- **`W ~ log` at `+∞`**: the principal Lambert branch is asymptotically
equivalent to the logarithm. -/
theorem principalLambertW_isEquivalent_log :
    principalLambertW ~[atTop] Real.log := by
  have hll : (Real.log ∘ Real.log) =o[atTop] (id ∘ Real.log) :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hbig : (principalLambertW - Real.log) =O[atTop]
      (Real.log ∘ Real.log) := by
    refine IsBigO.of_bound' ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have h1 := principalLambertW_le_log hx
    have h2 := log_sub_log_log_le_principalLambertW hx
    have hll0 : 0 ≤ Real.log (Real.log x) :=
      Real.log_nonneg (one_le_log_of_exp_one_le hx)
    rw [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hll0,
      abs_of_nonpos (by linarith : principalLambertW x - Real.log x ≤ 0)]
    linarith
  exact hbig.trans_isLittleO hll

/-- `W(x) → ∞` as `x → ∞`. -/
theorem tendsto_principalLambertW_atTop :
    Tendsto principalLambertW atTop atTop :=
  principalLambertW_isEquivalent_log.symm.tendsto_atTop Real.tendsto_log_atTop

/-- `W(x) / log x → 1` as `x → ∞`, by squeezing between
`1 - log log x / log x` and `1`. -/
theorem tendsto_principalLambertW_div_log :
    Tendsto (fun x : ℝ => principalLambertW x / Real.log x) atTop (𝓝 1) := by
  have hratio : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto
      Real.tendsto_log_atTop).tendsto_div_nhds_zero
  have hlow : Tendsto (fun x : ℝ => 1 - Real.log (Real.log x) / Real.log x)
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    ?_ ?_
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hL : 0 < Real.log x := by linarith [one_le_log_of_exp_one_le hx]
    have h2 := log_sub_log_log_le_principalLambertW hx
    have := div_le_div_of_nonneg_right h2 hL.le
    rwa [sub_div, div_self hL.ne'] at this
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hL : 0 < Real.log x := by linarith [one_le_log_of_exp_one_le hx]
    rw [div_le_one hL]
    exact principalLambertW_le_log hx

/-- **The two-term expansion at infinity**:
`W(x) = log x - log log x + o(1)`, i.e. `W(x) - (log x - log log x) → 0`.
Indeed `W - (L - ℓ) = ℓ - log W = -log (W / L)` and `W / L → 1`. -/
theorem tendsto_principalLambertW_sub_log_sub_log_log :
    Tendsto (fun x : ℝ =>
        principalLambertW x - (Real.log x - Real.log (Real.log x)))
      atTop (𝓝 0) := by
  have hlog : Tendsto
      (fun x : ℝ => -Real.log (principalLambertW x / Real.log x))
      atTop (𝓝 (-Real.log 1)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto.comp
      tendsto_principalLambertW_div_log).neg
  rw [Real.log_one, neg_zero] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hW := principalLambertW_pos hx0
  have hL : 0 < Real.log x := by linarith [one_le_log_of_exp_one_le hx]
  have h := principalLambertW_add_log hx0
  show -Real.log (principalLambertW x / Real.log x) =
    principalLambertW x - (Real.log x - Real.log (Real.log x))
  rw [Real.log_div hW.ne' hL.ne']
  linarith

end Fabius
