import FabiusFunction.FabiusLambertSaddle
import FabiusFunction.FabiusSharpConstant

/-!
# Exact Lambert-coordinate sharp main term

This file isolates the algebraic part of the corrected small-argument
asymptotic.  The remaining analytic input is solely the normalized Bromwich
kernel estimate.
-/

set_option autoImplicit false

namespace Fabius

/-- The corrected sharp main term in exact lower-Lambert coordinates. -/
noncomputable def fabiusSharpLambertMain (x : ℝ) : ℝ :=
  let lam := fabiusLambertPhase x;
  -(Real.log 2) / 2 * lam ^ 2 +
    (1 + Real.log 2 / 2) * lam - Real.log lam / 2 +
      fabiusSharpAsymptoticConstant + negativeLaplacePsi lam

/-- The lower-Lambert phase is positive on its natural branch domain. -/
theorem fabiusLambertPhase_pos {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    0 < fabiusLambertPhase x :=
  fabiusLambertPhase_pos_of_mem ⟨hx, (lt_div_iff₀
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 (by
      simpa only [mul_comm] using hsmall)⟩

/-- The exact saddle prefactor differs from the corrected Lambert main term
only by the exponentially small forward-tail error. -/
theorem fabiusLambertSaddleAction_eq
    {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    fabiusLambertRadius x * x +
          negativeLaplaceLog (fabiusLambertRadius x) -
          Real.log (2 * Real.pi * fabiusLambertPhase x) / 2 =
      fabiusSharpLambertMain x +
        negativeLaplaceTailError (fabiusLambertRadius x) := by
  let lam := fabiusLambertPhase x
  let r := fabiusLambertRadius x
  have hr : 0 < r := fabiusLambertRadius_pos x
  have hlam : 0 < lam := fabiusLambertPhase_pos hx hsmall
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hrx : r * x = lam := fabiusLambertRadius_mul_argument hx hsmall
  have hlogr : Real.log r = Real.log 2 * lam :=
    log_fabiusLambertRadius x
  have hlogbr : Real.logb 2 r = lam := by
    dsimp [r, lam, fabiusLambertRadius]
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
  rw [negativeLaplaceLog_exact_periodic_decomposition r hr]
  rw [hrx, hlogr, hlogbr]
  have hlogmul :
      Real.log (2 * Real.pi * lam) =
        Real.log (2 * Real.pi) + Real.log lam := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) Real.pi_ne_zero) hlam.ne']
  rw [hlogmul]
  have hmean := negativeLaplacePeriodicMean_sub_log_two_pi_half
  unfold fabiusSharpLambertMain negativeLaplacePsi
  dsimp [lam]
  rw [← hmean]
  dsimp [r]
  field_simp [hL]
  ring

end Fabius
