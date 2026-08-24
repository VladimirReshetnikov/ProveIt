import FabiusFunction.FabiusSmallArgumentScale
import FabiusFunction.FabiusLambertSaddle

/-!
# Comparing Lambert and logarithmic error scales

The exact lower-Lambert saddle phase is asymptotic to the logarithmic
coordinate.  For the sharp Fabius estimate it suffices to compare their
reciprocals by Big-O.  This module also converts that rate into the literal
`1 / (-log x)` scale at `x → 0⁺`.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

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

/-- Reciprocal logarithmic coordinate written in the source's `-log x` scale. -/
theorem smallArgumentLog_inv_eq {x : ℝ} (hx : 0 < x) :
    (fabiusSmallArgumentLog x)⁻¹ =
      Real.log 2 * (-Real.log x)⁻¹ := by
  unfold fabiusSmallArgumentLog Real.logb
  by_cases h : x = 1
  · subst x
    simp
  · have hlog : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx h
    have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlog, hL]

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
  have htarget : (fun x => (fabiusSmallArgumentLog x)⁻¹) =O[nhdsWithin 0 (Ioi 0)]
      (fun x => (-Real.log x)⁻¹) := by
    apply IsBigO.of_bound (Real.log 2)
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [smallArgumentLog_inv_eq hx, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by norm_num))]
  exact hs.trans htarget

end Fabius
