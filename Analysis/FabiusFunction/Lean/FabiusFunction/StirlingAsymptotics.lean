import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Stirling estimate used by the local K-fold Thue--Morse draft

This module records the precise `O(log n)` form of Stirling's formula invoked
between equations (7) and (8) of the draft.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace Fabius

/-- The source's Stirling estimate
`log(n!) = n log n - n + O(log n)` as `n → ∞`. -/
theorem log_factorial_sub_main_isBigO_log :
    (fun n : ℕ =>
      Real.log (n.factorial : ℝ) -
        ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))) =O[Filter.atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  have h_one :
      (fun _ : ℕ => (1 : ℝ)) =O[Filter.atTop]
        (fun n : ℕ => Real.log (n : ℝ)) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_const_log_atTop (c := (1 : ℝ))).isBigO.comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have h_log_stirling :
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) =O[Filter.atTop]
        (fun n : ℕ => Real.log (n : ℝ)) :=
    ((Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).isBigO_one ℝ).trans h_one
  have h_log_two_mul :
      (fun n : ℕ => Real.log (2 * (n : ℝ))) =O[Filter.atTop]
        (fun n : ℕ => Real.log (n : ℝ)) := by
    simpa [Function.comp_def] using
      (Real.isBigO_log_const_mul_log_atTop 2).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine (h_log_stirling.add (h_log_two_mul.const_mul_left (1 / 2))).congr_left ?_
  intro n
  rw [Stirling.log_stirlingSeq_formula]
  rcases n with _ | n
  · norm_num
  · rw [Real.log_div (by positivity) (by positivity), Real.log_exp]
    ring

end Fabius
