import FabiusFunction.FabiusSharpExactReduction
import FabiusFunction.FabiusLambertPhase
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The forward Laplace tail is flat on the Lambert scale

The exact sharp-saddle reduction contains the forward tail from the dyadic
Laplace product.  Its exponential decay in the saddle radius makes it smaller
than every inverse power of the lower-Lambert phase.  This module records that
arbitrary-order estimate once, so it can be discarded at every finite order
of the full Fabius expansion.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- Along `x = 2 ^ (-t)`, the forward product tail is smaller than every
inverse power of the exact lower-Lambert phase. -/
theorem negativeLaplaceTailError_dyadicLambert_isBigO_inv_pow
    (N : ℕ) :
    (fun t : ℝ => negativeLaplaceTailError
      (fabiusLambertRadius ((2 : ℝ) ^ (-t)))) =O[atTop]
        (fun t : ℝ =>
          (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹ ^ N) := by
  let b : ℝ → ℝ := fun t => fabiusLambertPhase ((2 : ℝ) ^ (-t))
  have hbtop : Tendsto b atTop atTop := by
    simpa [b, fabiusLambertPhase_dyadic] using
      tendsto_dyadicLambertPhase_atTop
  have htail :
      (fun t : ℝ => negativeLaplaceTailError
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))) =O[atTop]
        (fun t : ℝ => Real.exp (-(b t))) := by
    apply IsBigO.of_bound 4
    filter_upwards [hbtop.eventually_ge_atTop 1] with t hbt
    have hbernoulli :
        1 + b t * 1 ≤ (1 + (1 : ℝ)) ^ (b t) :=
      one_add_mul_self_le_rpow_one_add (s := (1 : ℝ))
        (by norm_num) hbt
    have hbr : b t ≤ fabiusLambertRadius ((2 : ℝ) ^ (-t)) := by
      rw [show (1 + (1 : ℝ)) = 2 by norm_num] at hbernoulli
      rw [fabiusLambertRadius_dyadic]
      rw [show b t = dyadicLambertPhase t by
        simp only [b, fabiusLambertPhase_dyadic]] at hbernoulli ⊢
      linarith
    have hrlog : Real.log 2 ≤
        fabiusLambertRadius ((2 : ℝ) ^ (-t)) := by
      have hloglt :=
        Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
          (by norm_num)
      norm_num at hloglt
      exact hloglt.le.trans (hbt.trans hbr)
    have hexp : Real.exp
        (-fabiusLambertRadius ((2 : ℝ) ^ (-t))) ≤
          Real.exp (-(b t)) := Real.exp_le_exp.mpr (neg_le_neg hbr)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact (abs_negativeLaplaceTailError_le_four_exp _ hrlog).trans
      (mul_le_mul_of_nonneg_left hexp (by norm_num))
  have hexp :
      (fun t : ℝ => Real.exp (-(b t))) =o[atTop]
        (fun t : ℝ => (b t) ^ (-(N : ℝ))) := by
    simpa only [Function.comp_def, neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop one_pos
        (-(N : ℝ))).comp_tendsto hbtop
  apply (htail.trans hexp.isBigO).congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [hbtop.eventually_gt_atTop 0] with t _hbt
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

end Fabius
