import FabiusFunction.FabiusLogSquaredAsymptotic
import FabiusFunction.FabiusSmallArgumentScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Comparison of the Fabius decay with an ordinary exponential

The quadratic logarithmic asymptotic implies the second qualitative
comparison stated in the K-fold Thue--Morse draft: although the Fabius
function is flat (and hence smaller than every power), it decays more slowly
than `exp (-c / x)` for every `c > 0`.

We state the result on the natural logarithmic scale `x = 2⁻ᵗ`, where
`exp (-c / x) = exp (-c * 2ᵗ)`, and then transfer it back to the
small-positive-argument filter.  Thus both the coordinate form used in the
proof and the direct comparison with `fabiusReal` are available as public
theorems.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

private theorem fabiusLogProfile_isBigO_sq
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusLogProfile F =O[atTop] (fun t : ℝ => t ^ 2) := by
  have hb := (fabiusLogProfile_normalized_tendsto F hF).isBigO_one ℝ
  have hm := hb.mul (isBigO_refl (fun t : ℝ => t ^ 2) atTop)
  apply hm.congr'
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  · exact Filter.Eventually.of_forall fun t => by simp

private theorem fabiusLogProfile_isLittleO_two_rpow
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusLogProfile F =o[atTop] (fun t : ℝ => (2 : ℝ) ^ t) := by
  apply (fabiusLogProfile_isBigO_sq F hF).trans_isLittleO
  apply (isLittleO_pow_exp_pos_mul_atTop 2
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).congr'
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact Filter.Eventually.of_forall fun t =>
      (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) t).symm

private theorem tendsto_profile_sub_exp_atBot
    (F : BoundedFabius) (hF : IsFabius F) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => fabiusLogProfile F t - c * (2 : ℝ) ^ t)
      atTop atBot := by
  have hbound := (fabiusLogProfile_isLittleO_two_rpow F hF).bound (half_pos hc)
  have hpow := tendsto_rpow_atTop_of_base_gt_one (2 : ℝ) (by norm_num)
  have hminor : Tendsto (fun t : ℝ => -(c / 2) * (2 : ℝ) ^ t) atTop atBot :=
    hpow.const_mul_atTop_of_neg (by linarith)
  apply tendsto_atBot_mono' atTop ?_ hminor
  filter_upwards [hbound] with t ht
  have hpow0 : 0 ≤ (2 : ℝ) ^ t :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hg : fabiusLogProfile F t ≤ c / 2 * (2 : ℝ) ^ t := by
    calc
      fabiusLogProfile F t ≤ ‖fabiusLogProfile F t‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ c / 2 * ‖(2 : ℝ) ^ t‖ := ht
      _ = c / 2 * (2 : ℝ) ^ t := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow0]
  linarith

private theorem fabiusLogPhi_eq_exp_neg_profile
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    fabiusLogPhi F t = Real.exp (-fabiusLogProfile F t) := by
  unfold fabiusLogProfile
  rw [neg_neg, Real.exp_log (fabiusLogPhi_pos F hF t)]

/-- On the dyadic logarithmic scale, the exponential `exp (-c / x)` is
little-o of the Fabius function for every positive `c`. -/
theorem exp_neg_two_rpow_isLittleO_fabiusLogPhi
    (F : BoundedFabius) (hF : IsFabius F) {c : ℝ} (hc : 0 < c) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ t)) =o[atTop]
      fabiusLogPhi F := by
  rw [isLittleO_iff_tendsto]
  · have hbot := tendsto_profile_sub_exp_atBot F hF hc
    have hexp := Real.tendsto_exp_atBot.comp hbot
    apply hexp.congr'
    filter_upwards with t
    change Real.exp (fabiusLogProfile F t - c * (2 : ℝ) ^ t) = _
    rw [fabiusLogPhi_eq_exp_neg_profile F hF, ← Real.exp_sub]
    congr 1
    ring
  · intro t hzero
    exact False.elim ((fabiusLogPhi_pos F hF t).ne' hzero)

/-- Canonical specialization of the exponential comparison. -/
theorem exp_neg_two_rpow_isLittleO_fabius {c : ℝ} (hc : 0 < c) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ t)) =o[atTop]
      fabiusLogPhi fabius :=
  exp_neg_two_rpow_isLittleO_fabiusLogPhi fabius fabius_spec hc

/-- On the original small-argument scale, `exp (-c / x)` is little-o of every
bounded/CDF Fabius solution as `x → 0⁺`, for every `c > 0`. -/
theorem exp_neg_div_isLittleO_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.exp (-c / x)) =o[nhdsWithin 0 (Set.Ioi 0)]
      fabiusReal F := by
  refine isLittleO_smallArgument_of_logScale
    (fun x : ℝ => Real.exp (-c / x)) (fabiusReal F) ?_
  have h := exp_neg_two_rpow_isLittleO_fabiusLogPhi F hF hc
  apply h.congr'
  · filter_upwards with t
    rw [div_eq_mul_inv, fabiusLogArgument_inv]
  · filter_upwards with t
    rfl

/-- Canonical small-argument specialization of the exponential comparison. -/
theorem exp_neg_div_isLittleO_fabius {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.exp (-c / x)) =o[nhdsWithin 0 (Set.Ioi 0)]
      fabiusReal fabius :=
  exp_neg_div_isLittleO_fabiusReal fabius fabius_spec hc

end Fabius
