import FabiusFunction.FabiusSmallArgumentScale
import FabiusFunction.FabiusLambertSaddle

/-!
# Comparing Lambert and logarithmic error scales

The exact lower-Lambert saddle phase is asymptotic to the logarithmic
coordinate.  This module records the sharp reciprocal ratio limit, extracts
the Big-O comparison used by the sharp Fabius estimate, and converts that rate
into the literal `1 / (-log x)` scale at `x → 0⁺`.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

/-- Sharp reciprocal form of the first-order Lambert asymptotic:
`t / dyadicLambertPhase t → 1`. -/
theorem dyadicLambertPhase_inv_mul_t_tendsto_one :
    Tendsto (fun t : ℝ => (dyadicLambertPhase t)⁻¹ * t) atTop (nhds 1) := by
  have h := dyadicLambertPhase_div_t_tendsto_one.inv₀ one_ne_zero
  have h' : Tendsto (fun t : ℝ => t / dyadicLambertPhase t)
      atTop (nhds (1 : ℝ)⁻¹) := by
    apply h.congr'
    filter_upwards with t
    rw [inv_div]
  simpa only [inv_one, div_eq_mul_inv, mul_comm] using h'

/-- The reciprocal lower-Lambert phase is `O(1/t)`. -/
theorem dyadicLambertPhase_inv_isBigO_inv :
    (fun t : ℝ => (dyadicLambertPhase t)⁻¹) =O[atTop]
      (fun t : ℝ => t⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_dyadicLambertPhase_domain,
      tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℝ)] with t hsmall hlam1 ht1
  have hfixed := dyadicLambertPhase_fixedPoint hsmall
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (dyadicLambertPhase t) :=
    Real.log_nonneg hlam1
  have htlam : t ≤ dyadicLambertPhase t := by
    calc
      t = dyadicLambertPhase t -
          Real.log (dyadicLambertPhase t) / Real.log 2 := hfixed.symm
      _ ≤ dyadicLambertPhase t :=
        sub_le_self _ (div_nonneg hlog hL.le)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hlam1)),
    abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one ht1)), one_mul]
  exact inv_anti₀ (lt_of_lt_of_le zero_lt_one ht1) htlam

/-- Reciprocal logarithmic coordinate written in the source's `-log x`
scale, for every real argument. -/
theorem smallArgumentLog_inv_eq_all (x : ℝ) :
    (fabiusSmallArgumentLog x)⁻¹ =
      Real.log 2 * (-Real.log x)⁻¹ := by
  unfold fabiusSmallArgumentLog Real.logb
  rw [inv_neg, inv_div, inv_neg, div_eq_mul_inv]
  ring

/-- Positive-argument compatibility form of
`smallArgumentLog_inv_eq_all`. -/
theorem smallArgumentLog_inv_eq {x : ℝ} (hx : 0 < x) :
    (fabiusSmallArgumentLog x)⁻¹ =
      Real.log 2 * (-Real.log x)⁻¹ := by
  by_cases h : x = 0
  · subst x
    norm_num at hx
  · exact smallArgumentLog_inv_eq_all x

/-- The reciprocal base-two logarithmic coordinate is bounded by the literal
reciprocal logarithmic scale on every filter. -/
theorem smallArgumentLog_inv_isBigO (l : Filter ℝ) :
    (fun x : ℝ => (fabiusSmallArgumentLog x)⁻¹) =O[l]
      (fun x => (-Real.log x)⁻¹) := by
  apply IsBigO.of_bound (Real.log 2)
  filter_upwards with x
  rw [smallArgumentLog_inv_eq_all x, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- Transfer an `O(1/λ)` logarithmic-scale estimate to the literal
`O(1/(-log x))` small-positive-argument rate. -/
theorem isBigO_smallArgument_log_of_lambertScale
    (f : ℝ → ℝ)
    (h : (fun t => f (fabiusLogArgument t)) =O[atTop]
      (fun t => (dyadicLambertPhase t)⁻¹)) :
    f =O[nhdsWithin 0 (Ioi 0)] (fun x => (-Real.log x)⁻¹) := by
  have ht := h.trans dyadicLambertPhase_inv_isBigO_inv
  have hs := isBigO_smallArgument_of_logScale f
    (fun x => (fabiusSmallArgumentLog x)⁻¹) (by
      apply ht.congr' Filter.EventuallyEq.rfl
      filter_upwards with t
      rw [fabiusSmallArgumentLog_logArgument])
  exact hs.trans (smallArgumentLog_inv_isBigO _)

end Fabius
