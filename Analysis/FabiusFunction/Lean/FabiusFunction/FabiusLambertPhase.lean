import FabiusFunction.LowerLambertW
import FabiusFunction.FabiusLogMainDefect

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

open Filter Set Function Topology Asymptotics
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

/-- Eventually every dyadic argument lies in the natural domain of the lower Lambert branch. -/
theorem eventually_dyadicLambertPhase_domain :
    ∀ᶠ t : ℝ in atTop,
      Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1) := by
  have htarget : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0), y < Real.exp (-1) :=
    (show ∀ᶠ y : ℝ in 𝓝 0, y < Real.exp (-1) from
      Iio_mem_nhds (Real.exp_pos (-1))).filter_mono nhdsWithin_le_nhds
  exact tendsto_log_two_mul_two_rpow_neg.eventually htarget

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

/-- Error after the first two elementary terms of the Lambert phase. -/
noncomputable def dyadicLambertRemainder (t : ℝ) : ℝ :=
  dyadicLambertPhase t - (t + Real.log t / Real.log 2)

/-- Relative perturbation appearing when the Lambert fixed-point equation is expanded. -/
noncomputable def dyadicLambertPerturbation (t : ℝ) : ℝ :=
  (Real.log t / Real.log 2 + dyadicLambertRemainder t) / t

theorem dyadicLambertRemainder_tendsto_zero :
    Tendsto dyadicLambertRemainder atTop (nhds 0) := by
  exact dyadicLambertPhase_sub_main_tendsto_zero

/-- The Lambert displacement remainder is the logarithm of the relative
perturbation, rescaled by `log 2`:
`dyadicLambertRemainder t = log (1 + dyadicLambertPerturbation t) / log 2`.

This is the exact algebraic identity behind every expansion of the Lambert
phase, obtained by rewriting the additive fixed-point equation
`dyadicLambertPhase_fixedPoint` as a statement about the ratio
`dyadicLambertPhase t / t`.  It is public rather than `private` because
downstream modules (notably `FabiusFunction.FabiusLambertHigherExpansion`)
need it to push the expansion past order `t⁻¹`. -/
theorem dyadicLambertRemainder_eq_log_perturbation {t : ℝ} (ht : 0 < t)
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1)) :
    dyadicLambertRemainder t =
      Real.log (1 + dyadicLambertPerturbation t) / Real.log 2 := by
  have hfixed := dyadicLambertPhase_fixedPoint hsmall
  have hphase : 0 < dyadicLambertPhase t := by
    have heq := dyadicLambertPhase_eq9 hsmall
    have hp : 0 < (2 : ℝ) ^ (-dyadicLambertPhase t) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have : 0 < dyadicLambertPhase t * (2 : ℝ) ^ (-dyadicLambertPhase t) :=
      heq.symm ▸ Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  have hratio : 1 + dyadicLambertPerturbation t = dyadicLambertPhase t / t := by
    unfold dyadicLambertPerturbation dyadicLambertRemainder
    field_simp
    ring
  rw [hratio, Real.log_div hphase.ne' ht.ne']
  unfold dyadicLambertRemainder
  have hdiff : dyadicLambertPhase t - t =
      Real.log (dyadicLambertPhase t) / Real.log 2 := by linarith
  rw [show dyadicLambertPhase t - (t + Real.log t / Real.log 2) =
      (dyadicLambertPhase t - t) - Real.log t / Real.log 2 by ring,
    hdiff]
  ring

theorem dyadicLambertPerturbation_tendsto_zero :
    Tendsto dyadicLambertPerturbation atTop (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hfirst := hlog.div_const (Real.log 2)
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hsecond := dyadicLambertRemainder_tendsto_zero.mul hinv
  have hadd := hfirst.add hsecond
  convert hadd using 1
  · funext t
    unfold dyadicLambertPerturbation
    field_simp
  · simp

private lemma dyadicLambertRemainder_isBigO_one :
    dyadicLambertRemainder =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  dyadicLambertRemainder_tendsto_zero.isBigO_one ℝ

private lemma dyadicLambertNumerator_isBigO_log :
    (fun t : ℝ => Real.log t / Real.log 2 + dyadicLambertRemainder t) =O[atTop]
      Real.log := by
  have hfirst : (fun t : ℝ => Real.log t / Real.log 2) =O[atTop] Real.log := by
    exact ((isBigO_refl Real.log atTop).const_mul_left (Real.log 2)⁻¹).congr'
      (Filter.Eventually.of_forall fun t => by simp [div_eq_mul_inv, mul_comm])
      (Filter.Eventually.of_forall fun _ => rfl)
  have hone : (fun _ : ℝ => (1 : ℝ)) =O[atTop] Real.log :=
    Real.isLittleO_const_log_atTop.isBigO
  exact hfirst.add (dyadicLambertRemainder_isBigO_one.trans hone)

private lemma dyadicLambertPerturbation_isBigO_log_div :
    dyadicLambertPerturbation =O[atTop] (fun t : ℝ => Real.log t / t) := by
  have h := dyadicLambertNumerator_isBigO_log.mul
    (isBigO_refl (fun t : ℝ => t⁻¹) atTop)
  exact h.congr'
    (Filter.Eventually.of_forall fun t => by
      simp [dyadicLambertPerturbation, div_eq_mul_inv])
    (Filter.Eventually.of_forall fun t => by simp [div_eq_mul_inv])

private lemma log_div_sq_isBigO_one_div :
    (fun t : ℝ => (Real.log t / t) ^ 2) =O[atTop] (fun t : ℝ => 1 / t) := by
  have hlog := (Real.isLittleO_pow_log_id_atTop (n := 2)).mul_isBigO
    (isBigO_refl (fun t : ℝ => t⁻¹ ^ 2) atTop)
  have h : (fun t : ℝ => Real.log t ^ 2 * t⁻¹ ^ 2) =O[atTop]
      (fun t : ℝ => t * t⁻¹ ^ 2) := hlog.isBigO
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
    ((eventually_ne_atTop (0 : ℝ)).mono fun t _ht => ?_)
  · change Real.log t ^ 2 * t⁻¹ ^ 2 = (Real.log t / t) ^ 2
    rw [div_pow]
    ring
  · simp only
    field_simp

private lemma dyadicLambertPerturbation_sq_isBigO_one_div :
    (fun t : ℝ => dyadicLambertPerturbation t ^ 2) =O[atTop]
      (fun t : ℝ => 1 / t) :=
  dyadicLambertPerturbation_isBigO_log_div.pow 2 |>.trans
    log_div_sq_isBigO_one_div

/-- Error after retaining the phase displacement of order `log t / t`. -/
noncomputable def dyadicLambertRefinedRemainder (t : ℝ) : ℝ :=
  dyadicLambertRemainder t - Real.log t / (Real.log 2) ^ 2 / t

/-- Quantitative three-term expansion of the exact Lambert phase:

`lambda(t) = t + log₂ t + log t / ((log 2)^2 t) + O(1/t)`.

This is the accuracy required to sample a nonconstant periodic correction while preserving an
`O(1/t)` final error. -/
theorem dyadicLambertRefinedRemainder_isBigO :
    dyadicLambertRefinedRemainder =O[atTop] (fun t : ℝ => 1 / t) := by
  have hlogError :
      (fun t : ℝ => Real.log (1 + dyadicLambertPerturbation t) -
        dyadicLambertPerturbation t) =O[atTop]
          (fun t : ℝ => dyadicLambertPerturbation t ^ 2) :=
    real_log_first_order_isBigO.comp_tendsto
      dyadicLambertPerturbation_tendsto_zero
  have hlogError' :
      (fun t : ℝ => (Real.log (1 + dyadicLambertPerturbation t) -
        dyadicLambertPerturbation t) / Real.log 2) =O[atTop]
          (fun t : ℝ => 1 / t) := by
    exact (hlogError.const_mul_left (Real.log 2)⁻¹).congr'
      (Filter.Eventually.of_forall fun t => by simp [div_eq_mul_inv, mul_comm])
      (Filter.Eventually.of_forall fun _ => rfl) |>.trans
        dyadicLambertPerturbation_sq_isBigO_one_div
  have honeDiv : (fun t : ℝ => 1 / (Real.log 2 * t)) =O[atTop]
      (fun t : ℝ => 1 / t) := by
    exact ((isBigO_refl (fun t : ℝ => 1 / t) atTop).const_mul_left
      (Real.log 2)⁻¹).congr'
        (Filter.Eventually.of_forall fun t => by
          simp [div_eq_mul_inv]
          ring)
        (Filter.Eventually.of_forall fun _ => rfl)
  have hremDiv : (fun t : ℝ =>
      dyadicLambertRemainder t / (Real.log 2 * t)) =O[atTop]
        (fun t : ℝ => 1 / t) := by
    have h := dyadicLambertRemainder_isBigO_one.mul honeDiv
    exact h.congr'
      (Filter.Eventually.of_forall fun t => by simp [div_eq_mul_inv])
      (Filter.Eventually.of_forall fun t => by simp)
  have hsum := hlogError'.add hremDiv
  refine hsum.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_dyadicLambertPhase_domain] with t ht hsmall
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hr := dyadicLambertRemainder_eq_log_perturbation ht hsmall
  have hlog : Real.log (1 + dyadicLambertPerturbation t) =
      dyadicLambertRemainder t * Real.log 2 := by
    rw [hr]
    field_simp
  rw [dyadicLambertRefinedRemainder, hlog]
  unfold dyadicLambertPerturbation
  field_simp
  ring

end Fabius
