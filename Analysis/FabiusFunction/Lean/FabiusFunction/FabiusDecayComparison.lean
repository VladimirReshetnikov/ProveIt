import FabiusFunction.FabiusLogSquaredAsymptotic
import FabiusFunction.FabiusSmallArgumentScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Comparison of the Fabius decay with inverse-power exponentials

The K-fold Thue--Morse draft observes that, although the Fabius
function is flat (and hence smaller than every power), it decays more slowly
than `exp (-c / x)` for every `c > 0`.  The quadratic logarithmic asymptotic
strengthens this comparison: `exp (-c / x ^ β)` is little-o of the Fabius
function for every `c > 0` and every `β > 0`.

We state the result on the natural logarithmic scale `x = 2⁻ᵗ`, where
`exp (-c / x ^ β) = exp (-c * 2 ^ (β * t))`, and then transfer it
back to the small-positive-argument filter.  Thus both the coordinate form
used in the proof and the direct comparison with `fabiusReal` are available
as public theorems.  The earlier `β = 1` declarations remain as compatibility
specializations.
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

/-- The negative-log Fabius profile grows more slowly than every positive-rate
dyadic exponential `2 ^ (β * t)`. -/
theorem fabiusLogProfile_isLittleO_two_rpow_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {β : ℝ} (hβ : 0 < β) :
    fabiusLogProfile F =o[atTop]
      (fun t : ℝ => (2 : ℝ) ^ (β * t)) := by
  apply (fabiusLogProfile_isBigO_sq F hF).trans_isLittleO
  apply (isLittleO_pow_exp_pos_mul_atTop 2
    (mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hβ)).congr'
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact Filter.Eventually.of_forall fun t => by
      change Real.exp (Real.log 2 * β * t) = (2 : ℝ) ^ (β * t)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

private theorem tendsto_profile_sub_exp_atBot
    (F : BoundedFabius) (hF : IsFabius F)
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    Tendsto
      (fun t : ℝ => fabiusLogProfile F t - c * (2 : ℝ) ^ (β * t))
      atTop atBot := by
  have hbound :=
    (fabiusLogProfile_isLittleO_two_rpow_mul F hF hβ).bound (half_pos hc)
  have hpow :
      Tendsto (fun t : ℝ => (2 : ℝ) ^ (β * t)) atTop atTop := by
    simpa only [Function.comp_def, id_eq] using
      (tendsto_rpow_atTop_of_base_gt_one (2 : ℝ) (by norm_num)).comp
        (tendsto_id.const_mul_atTop hβ)
  have hminor :
      Tendsto (fun t : ℝ => -(c / 2) * (2 : ℝ) ^ (β * t))
        atTop atBot :=
    hpow.const_mul_atTop_of_neg (by linarith)
  apply tendsto_atBot_mono' atTop ?_ hminor
  filter_upwards [hbound] with t ht
  have hpow0 : 0 ≤ (2 : ℝ) ^ (β * t) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hg : fabiusLogProfile F t ≤ c / 2 * (2 : ℝ) ^ (β * t) := by
    calc
      fabiusLogProfile F t ≤ ‖fabiusLogProfile F t‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ c / 2 * ‖(2 : ℝ) ^ (β * t)‖ := ht
      _ = c / 2 * (2 : ℝ) ^ (β * t) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow0]
  linarith

private theorem fabiusLogPhi_eq_exp_neg_profile
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    fabiusLogPhi F t = Real.exp (-fabiusLogProfile F t) := by
  unfold fabiusLogProfile
  rw [neg_neg, Real.exp_log (fabiusLogPhi_pos F hF t)]

/-- On the dyadic logarithmic scale, `exp (-c * 2 ^ (β * t))` is little-o of
the Fabius function whenever `c > 0` and `β > 0`. -/
theorem exp_neg_two_rpow_mul_isLittleO_fabiusLogPhi
    (F : BoundedFabius) (hF : IsFabius F)
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ (β * t))) =o[atTop]
      fabiusLogPhi F := by
  rw [isLittleO_iff_tendsto]
  · have hbot := tendsto_profile_sub_exp_atBot F hF hc hβ
    have hexp := Real.tendsto_exp_atBot.comp hbot
    apply hexp.congr'
    filter_upwards with t
    change Real.exp (fabiusLogProfile F t - c * (2 : ℝ) ^ (β * t)) = _
    rw [fabiusLogPhi_eq_exp_neg_profile F hF, ← Real.exp_sub]
    congr 1
    ring
  · intro t hzero
    exact False.elim ((fabiusLogPhi_pos F hF t).ne' hzero)

/-- The canonical Fabius function satisfies the positive-rate dyadic
exponential comparison. -/
theorem exp_neg_two_rpow_mul_isLittleO_fabius
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ (β * t))) =o[atTop]
      fabiusLogPhi fabius :=
  exp_neg_two_rpow_mul_isLittleO_fabiusLogPhi fabius fabius_spec hc hβ

/-- Compatibility specialization at `β = 1` on the dyadic logarithmic scale. -/
theorem exp_neg_two_rpow_isLittleO_fabiusLogPhi
    (F : BoundedFabius) (hF : IsFabius F) {c : ℝ} (hc : 0 < c) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ t)) =o[atTop]
      fabiusLogPhi F := by
  simpa only [one_mul] using
    exp_neg_two_rpow_mul_isLittleO_fabiusLogPhi
      F hF (β := 1) hc zero_lt_one

/-- Canonical compatibility specialization at `β = 1` on the dyadic
logarithmic scale. -/
theorem exp_neg_two_rpow_isLittleO_fabius {c : ℝ} (hc : 0 < c) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ t)) =o[atTop]
      fabiusLogPhi fabius := by
  simpa only [one_mul] using
    exp_neg_two_rpow_mul_isLittleO_fabius (β := 1) hc zero_lt_one

/-- On the original small-argument scale, every `exp (-c / x ^ β)` is
little-o of every bounded/CDF Fabius solution for `c > 0` and `β > 0`. -/
theorem exp_neg_div_rpow_isLittleO_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F)
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun x : ℝ => Real.exp (-c / x ^ β)) =o[nhdsWithin 0 (Set.Ioi 0)]
      fabiusReal F := by
  refine isLittleO_smallArgument_of_logScale
    (fun x : ℝ => Real.exp (-c / x ^ β)) (fabiusReal F) ?_
  have h := exp_neg_two_rpow_mul_isLittleO_fabiusLogPhi F hF hc hβ
  apply h.congr'
  · filter_upwards with t
    have hpow :
        fabiusLogArgument t ^ β = ((2 : ℝ) ^ (β * t))⁻¹ := by
      calc
        fabiusLogArgument t ^ β
            = ((2 : ℝ) ^ (-t)) ^ β := by
                rw [fabiusLogArgument]
        _ = (2 : ℝ) ^ ((-t) * β) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-t) β).symm
        _ = (2 : ℝ) ^ (-(β * t)) := by
          congr 1
          ring
        _ = ((2 : ℝ) ^ (β * t))⁻¹ :=
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
    rw [hpow, div_inv_eq_mul]
  · filter_upwards with t
    rfl

/-- Compatibility specialization at `β = 1` for every bounded/CDF Fabius
solution on the original small-argument scale. -/
theorem exp_neg_div_isLittleO_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.exp (-c / x)) =o[nhdsWithin 0 (Set.Ioi 0)]
      fabiusReal F := by
  simpa only [Real.rpow_one] using
    exp_neg_div_rpow_isLittleO_fabiusReal
      F hF (β := 1) hc zero_lt_one

/-- The canonical Fabius function dominates every inverse-power exponential
`exp (-c / x ^ β)` at the origin whenever `c > 0` and `β > 0`. -/
theorem exp_neg_div_rpow_isLittleO_fabius
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun x : ℝ => Real.exp (-c / x ^ β)) =o[nhdsWithin 0 (Set.Ioi 0)]
      fabiusReal fabius :=
  exp_neg_div_rpow_isLittleO_fabiusReal fabius fabius_spec hc hβ

/-- Canonical small-argument compatibility specialization at `β = 1`. -/
theorem exp_neg_div_isLittleO_fabius {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.exp (-c / x)) =o[nhdsWithin 0 (Set.Ioi 0)]
      fabiusReal fabius := by
  simpa only [Real.rpow_one] using
    exp_neg_div_rpow_isLittleO_fabius (β := 1) hc zero_lt_one

end Fabius
