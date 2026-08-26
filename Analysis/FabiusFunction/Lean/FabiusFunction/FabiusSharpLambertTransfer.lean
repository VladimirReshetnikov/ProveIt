import FabiusFunction.FabiusSharpLambertMain
import FabiusFunction.FabiusSaddleReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Transfer from the Lambert saddle kernel to the sharp Fabius asymptotic

This module discharges the algebraic and filter-theoretic work after the
normalized Bromwich kernel has been estimated.  Along the real logarithmic
scale `x = 2 ^ (-t)`, a relative kernel error of order `1 / lambda` implies
the corrected sharp logarithmic asymptotic with the same error.

The exponentially small forward tail in the exact negative-Laplace
decomposition is absorbed unconditionally.  Bernoulli's inequality and the
standard exponential-versus-power comparison show that this tail is smaller
than every inverse power of `lambda`; the order-one transfer estimate is its
immediate specialization.
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

/-- Along the lower-Lambert logarithmic coordinate, the forward product tail
is `O(1 / lambda)`. -/
theorem negativeLaplaceTailError_dyadicLambert_isBigO_inv :
    (fun t : ℝ => negativeLaplaceTailError
      (fabiusLambertRadius ((2 : ℝ) ^ (-t)))) =O[atTop]
        (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹) := by
  simpa only [pow_one] using
    negativeLaplaceTailError_dyadicLambert_isBigO_inv_pow 1

/-- A normalized `O(1 / lambda)` estimate for the Bromwich saddle kernel at
the explicit lower-Lambert coordinates implies the corrected sharp Fabius
asymptotic along `x = 2 ^ (-t)`. -/
theorem log_fabius_dyadicReal_sub_sharpLambertMain_isBigO_of_kernelMass
    (F : BoundedFabius) (hF : IsFabius F)
    (hkernel :
      (fun t : ℝ => fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (fabiusLambertPhase ((2 : ℝ) ^ (-t))) - 1) =O[atTop]
        (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹)) :
    (fun t : ℝ => Real.log (fabiusReal F ((2 : ℝ) ^ (-t))) -
        fabiusSharpLambertMain ((2 : ℝ) ^ (-t))) =O[atTop]
      (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹) := by
  let x : ℝ → ℝ := fun t => (2 : ℝ) ^ (-t)
  let r : ℝ → ℝ := fun t => fabiusLambertRadius (x t)
  let b : ℝ → ℝ := fun t => fabiusLambertPhase (x t)
  have hr : ∀ᶠ t in atTop, 0 < r t :=
    Filter.Eventually.of_forall fun t => fabiusLambertRadius_pos (x t)
  have hbpos : ∀ᶠ t in atTop, 0 < b t := by
    filter_upwards [eventually_dyadicLambertPhase_domain] with t hsmall
    exact fabiusLambertPhase_pos (Real.rpow_pos_of_pos (by norm_num) _) hsmall
  have hbinfty : Tendsto b atTop atTop := by
    simpa [b, x, fabiusLambertPhase_dyadic] using
      tendsto_dyadicLambertPhase_atTop
  have hFxpos : ∀ᶠ t in atTop, 0 < fabiusReal F (x t) :=
    Filter.Eventually.of_forall fun t =>
      fabius_pos_of_pos F hF (Real.rpow_pos_of_pos (by norm_num) _)
  have hsaddle := fabius_saddle_log_error_isBigO atTop F hF x r b
    hr hbpos hbinfty hFxpos (by simpa [x, r, b] using hkernel)
  have htail :
      (fun t : ℝ => negativeLaplaceTailError (r t)) =O[atTop]
        (fun t : ℝ => (b t)⁻¹) := by
    simpa [x, r, b] using negativeLaplaceTailError_dyadicLambert_isBigO_inv
  have haction :
      (fun t : ℝ =>
        (r t * x t + negativeLaplaceLog (r t) -
            Real.log (2 * Real.pi * b t) / 2) -
          fabiusSharpLambertMain (x t)) =O[atTop]
        (fun t : ℝ => (b t)⁻¹) := by
    apply htail.congr'
    · filter_upwards [eventually_dyadicLambertPhase_domain] with t hsmall
      rw [fabiusLambertSaddleAction_eq
        (Real.rpow_pos_of_pos (by norm_num) _) hsmall]
      simp only [r, x]
      ring
    · exact Filter.EventuallyEq.rfl
  have hsum := hsaddle.add haction
  apply hsum.congr'
  · filter_upwards with t
    dsimp [x, r, b]
    ring
  · exact Filter.EventuallyEq.rfl

end Fabius
