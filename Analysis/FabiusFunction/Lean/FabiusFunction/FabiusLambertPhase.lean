import FabiusFunction.LowerLambertW

/-!
# The Lambert phase in the sharp Fabius asymptotic

The logarithmic periodic correction in the negative Laplace product is not sampled at the
naive dyadic coordinate `t`.  Its natural saddle coordinate is the lower-Lambert solution
`lambda` of

`lambda * 2 ^ (-lambda) = 2 ^ (-t)`.

This file defines that coordinate, proves its exact fixed-point equation, and records its
first two asymptotic terms.  The exact coordinate will be kept in the final sharp theorem;
using it avoids losing a logarithmic factor in the claimed remainder.
-/

set_option autoImplicit false

open Filter Set Function Topology
open scoped Topology

namespace Fabius

/-- The lower-Lambert saddle coordinate corresponding to the dyadic logarithmic scale `t`. -/
noncomputable def dyadicLambertPhase (t : ℝ) : ℝ :=
  paperLambertN ((2 : ℝ) ^ (-t))

/-- The defining saddle equation for `dyadicLambertPhase`. -/
theorem dyadicLambertPhase_eq9 {t : ℝ}
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1)) :
    dyadicLambertPhase t * (2 : ℝ) ^ (-dyadicLambertPhase t) =
      (2 : ℝ) ^ (-t) := by
  exact paperLambertN_eq9 (Real.rpow_pos_of_pos (by norm_num) _)
    hsmall

/-- Additive fixed-point form of the saddle equation. -/
theorem dyadicLambertPhase_fixedPoint {t : ℝ}
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1)) :
    dyadicLambertPhase t - Real.log (dyadicLambertPhase t) / Real.log 2 = t := by
  have heq := dyadicLambertPhase_eq9 hsmall
  have hrpow : 0 < (2 : ℝ) ^ (-dyadicLambertPhase t) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hphase : 0 < dyadicLambertPhase t := by
    have : 0 < dyadicLambertPhase t * (2 : ℝ) ^ (-dyadicLambertPhase t) :=
      heq.symm ▸ Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  have hlog := congrArg Real.log heq
  rw [Real.log_mul hphase.ne' hrpow.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  linarith

private lemma tendsto_log_two_mul_two_rpow_neg :
    Tendsto (fun t : ℝ => Real.log 2 * (2 : ℝ) ^ (-t)) atTop
      (nhdsWithin 0 (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hlin : Tendsto (fun t : ℝ => -t * Real.log 2) atTop atBot := by
      have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hmul : Tendsto (fun t : ℝ => Real.log 2 * t) atTop atTop :=
        tendsto_id.const_mul_atTop hpos
      simpa only [Function.comp_def, neg_mul, mul_comm] using
        tendsto_neg_atTop_atBot.comp hmul
    have hpow : Tendsto (fun t : ℝ => (2 : ℝ) ^ (-t)) atTop (nhds 0) := by
      simp_rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [Function.comp_def, mul_comm] using Real.tendsto_exp_atBot.comp hlin
    simpa using tendsto_const_nhds.mul hpow
  · filter_upwards with t
    exact mul_pos (Real.log_pos (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)

private lemma log_log_two_mul_two_rpow_neg (t : ℝ) :
    Real.log (Real.log 2 * (2 : ℝ) ^ (-t)) =
      Real.log (Real.log 2) - t * Real.log 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.log_mul hL.ne' hpow.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  ring_nf

private lemma tendsto_lambert_deterministic_remainder :
    Tendsto
      (fun t : ℝ =>
        -(Real.log (Real.log 2 * (2 : ℝ) ^ (-t)) -
            Real.log |Real.log (Real.log 2 * (2 : ℝ) ^ (-t))|) / Real.log 2 -
          (t + Real.log t / Real.log 2))
      atTop (nhds 0) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htL : Tendsto (fun t : ℝ => t * Real.log 2) atTop atTop :=
    tendsto_id.atTop_mul_const hL
  have hinv : Tendsto (fun t : ℝ => (t * Real.log 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htL
  have hratio : Tendsto
      (fun t : ℝ => 1 - Real.log (Real.log 2) * (t * Real.log 2)⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  have hlogratio : Tendsto
      (fun t : ℝ => Real.log (1 - Real.log (Real.log 2) * (t * Real.log 2)⁻¹))
      atTop (nhds 0) := by
    simpa using hratio.log one_ne_zero
  have hscaled := hlogratio.div_const (Real.log 2)
  have hscaled' : Tendsto
      (fun t : ℝ => Real.log (1 - Real.log (Real.log 2) *
        (t * Real.log 2)⁻¹) / Real.log 2) atTop (nhds 0) := by
    simpa using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
      htL.eventually (eventually_gt_atTop (Real.log (Real.log 2)))] with t ht htlog
  rw [log_log_two_mul_two_rpow_neg]
  have hneg : Real.log (Real.log 2) - t * Real.log 2 < 0 := by linarith
  rw [abs_of_neg hneg]
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hL0 : Real.log 2 ≠ 0 := hL.ne'
  have hnum : 0 < t * Real.log 2 - Real.log (Real.log 2) := by linarith
  rw [show 1 - Real.log (Real.log 2) * (t * Real.log 2)⁻¹ =
      (t * Real.log 2 - Real.log (Real.log 2)) / (t * Real.log 2) by
        field_simp]
  rw [Real.log_div hnum.ne' (mul_ne_zero ht0 hL0)]
  rw [Real.log_mul ht0 hL0]
  field_simp
  ring_nf

/-- The Lambert phase is `t + log₂ t + o(1)` on the dyadic logarithmic scale. -/
theorem dyadicLambertPhase_sub_main_tendsto_zero :
    Tendsto
      (fun t : ℝ => dyadicLambertPhase t - (t + Real.log t / Real.log 2))
      atTop (nhds 0) := by
  have hrem := tendsto_lowerLambertW_expansion.comp
    tendsto_log_two_mul_two_rpow_neg
  have hscaled := hrem.neg.div_const (Real.log 2)
  have hdet := tendsto_lambert_deterministic_remainder
  have hadd := hscaled.add hdet
  have hadd' : Tendsto
      (fun t : ℝ =>
        -((fun eps : ℝ => lowerLambertW (-eps) -
            (Real.log eps - Real.log |Real.log eps|))
            (Real.log 2 * (2 : ℝ) ^ (-t))) / Real.log 2 +
          (-(Real.log (Real.log 2 * (2 : ℝ) ^ (-t)) -
              Real.log |Real.log (Real.log 2 * (2 : ℝ) ^ (-t))|) / Real.log 2 -
            (t + Real.log t / Real.log 2)))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hadd
  refine hadd'.congr' ?_
  filter_upwards with t
  unfold dyadicLambertPhase paperLambertN
  ring_nf

end Fabius
