import FabiusFunction.FabiusSharpLambertMain
import FabiusFunction.FabiusSaddleReduction

/-!
# Transfer from the Lambert saddle kernel to the sharp Fabius asymptotic

This module discharges the algebraic and filter-theoretic work after the
normalized Bromwich kernel has been estimated.  Along the real logarithmic
scale `x = 2 ^ (-t)`, a relative kernel error of order `1 / lambda` implies
the corrected sharp logarithmic asymptotic with the same error.

The exponentially small forward tail in the exact negative-Laplace
decomposition is absorbed unconditionally.  Bernoulli's inequality gives
`lambda <= 2 ^ lambda` eventually, after which elementary exponential bounds
show that this tail is `O(1 / lambda)`.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- Along the lower-Lambert logarithmic coordinate, the forward product tail
is `O(1 / lambda)`. -/
theorem negativeLaplaceTailError_dyadicLambert_isBigO_inv :
    (fun t : ℝ => negativeLaplaceTailError
      (fabiusLambertRadius ((2 : ℝ) ^ (-t)))) =O[atTop]
        (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹) := by
  rw [isBigO_iff]
  refine ⟨4, ?_⟩
  filter_upwards [eventually_dyadicLambertPhase_domain,
      tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1] with t hsmall hlam1
  have hx : 0 < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) _
  have hlam : 0 < fabiusLambertPhase ((2 : ℝ) ^ (-t)) :=
    fabiusLambertPhase_pos hx hsmall
  have hr : 0 < fabiusLambertRadius ((2 : ℝ) ^ (-t)) :=
    fabiusLambertRadius_pos _
  have hlamr :
      fabiusLambertPhase ((2 : ℝ) ^ (-t)) ≤
        fabiusLambertRadius ((2 : ℝ) ^ (-t)) := by
    have hbernoulli :
        1 + fabiusLambertPhase ((2 : ℝ) ^ (-t)) * 1 ≤
          (1 + (1 : ℝ)) ^ fabiusLambertPhase ((2 : ℝ) ^ (-t)) :=
      one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
        (by simpa [fabiusLambertPhase_dyadic] using hlam1)
    rw [show (1 + (1 : ℝ)) = 2 by norm_num] at hbernoulli
    change 1 + fabiusLambertPhase ((2 : ℝ) ^ (-t)) * 1 ≤
      fabiusLambertRadius ((2 : ℝ) ^ (-t)) at hbernoulli
    linarith
  have hrlog : Real.log 2 ≤ fabiusLambertRadius ((2 : ℝ) ^ (-t)) := by
    have hloglt :=
      Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at hloglt
    exact hloglt.le.trans (hlam1.trans hlamr)
  have hexpInv :
      Real.exp (-fabiusLambertRadius ((2 : ℝ) ^ (-t))) ≤
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hr).2
      ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
        (Real.add_one_le_exp _))
  have hrInv :
      (fabiusLambertRadius ((2 : ℝ) ^ (-t)))⁻¹ ≤
        (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹ :=
    (inv_le_inv₀ hr hlam).2 hlamr
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
  exact (abs_negativeLaplaceTailError_le_four_exp _ hrlog).trans
    (mul_le_mul_of_nonneg_left (hexpInv.trans hrInv) (by norm_num))

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
