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

private lemma log_stirlingSeq_telescope_le (n m : ℕ) (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + m)) ≤
      (1 : ℝ) / (12 * n) := by
  have hstep (j : ℕ) :
      Real.log (Stirling.stirlingSeq (n + j)) -
          Real.log (Stirling.stirlingSeq (n + j + 1)) ≤
        (1 : ℝ) / (12 * (n + j) * (n + j + 1)) := by
    simpa [Nat.add_assoc] using Stirling.log_stirlingSeq_sdiff_le (n + j)
  have hsum := Finset.sum_le_sum fun j (_hj : j ∈ Finset.range m) => hstep j
  have htel :
      (∑ j ∈ Finset.range m,
          (Real.log (Stirling.stirlingSeq (n + j)) -
            Real.log (Stirling.stirlingSeq (n + j + 1)))) =
        Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + m)) := by
    simpa [Nat.add_assoc] using
      (Finset.sum_range_sub' (f := fun j : ℕ =>
        Real.log (Stirling.stirlingSeq (n + j))) m)
  have hrecip (j : ℕ) :
      (1 : ℝ) / (12 * (n + j) * (n + j + 1)) =
        (1 : ℝ) / (12 * (n + j)) - (1 : ℝ) / (12 * (n + j + 1)) := by
    have hnj : (n + j : ℝ) ≠ 0 := by positivity
    have hnjs : (n + j + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [hrecip] at hsum
  have hrectel :
      (∑ j ∈ Finset.range m,
          ((1 : ℝ) / (12 * (n + j)) -
            (1 : ℝ) / (12 * (n + j + 1)))) =
        (1 : ℝ) / (12 * n) - (1 : ℝ) / (12 * (n + m)) := by
    convert
      (Finset.sum_range_sub' (f := fun j : ℕ =>
        (1 : ℝ) / (12 * (n + j))) m) using 1 <;>
      push_cast <;> ring_nf
  rw [htel, hrectel] at hsum
  calc
    Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + m)) ≤
      (1 : ℝ) / (12 * n) - (1 : ℝ) / (12 * (n + m)) := by
        simpa [Nat.add_assoc] using hsum
    _ ≤ (1 : ℝ) / (12 * n) := by
      have hnonneg : 0 ≤ (1 : ℝ) / (12 * (n + m)) := by positivity
      linarith

/-- Robbins' sharp logarithmic remainder bound for the Stirling sequence. -/
theorem log_stirlingSeq_sub_half_log_pi_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 ∧
      Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 ≤
        (1 : ℝ) / (12 * n) := by
  have hsqrt : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
    rw [Real.log_sqrt (le_of_lt Real.pi_pos)]
  constructor
  · rw [← hsqrt, sub_nonneg]
    exact Real.log_le_log (by positivity)
      (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  · rw [← hsqrt]
    have hlim : Tendsto
        (fun m : ℕ => Real.log (Stirling.stirlingSeq (n + m))) atTop
        (nhds (Real.log (Real.sqrt Real.pi))) := by
      exact (Real.continuousAt_log (by positivity)).tendsto.comp
        (Stirling.tendsto_stirlingSeq_sqrt_pi.comp
          (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n))
    have hdiff : Tendsto
        (fun m : ℕ => Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + m))) atTop
        (nhds (Real.log (Stirling.stirlingSeq n) -
          Real.log (Real.sqrt Real.pi))) :=
      tendsto_const_nhds.sub hlim
    exact le_of_tendsto hdiff (Eventually.of_forall fun m =>
      log_stirlingSeq_telescope_le n m hn)

/-- The sharp logarithmic Stirling formula with explicit error `1 / (12n)`. -/
theorem log_factorial_sub_stirlingMain_bounds (n : ℕ) (hn : 1 ≤ n) :
    let remainder := Real.log (n.factorial : ℝ) -
      ((n : ℝ) * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2)
    0 ≤ remainder ∧ remainder ≤ (1 : ℝ) / (12 * n) := by
  dsimp
  have hformula := Stirling.log_stirlingSeq_formula n
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlogdiv : Real.log ((n : ℝ) / Real.exp 1) = Real.log n - 1 := by
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp]
  have hlogtwo : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) hn0]
  have hlogtwopi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
  rw [hlogdiv, hlogtwo] at hformula
  have hremainder :
      Real.log (n.factorial : ℝ) -
          ((n : ℝ) * Real.log n - n + Real.log n / 2 +
            Real.log (2 * Real.pi) / 2) =
        Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 := by
    rw [hlogtwopi, hformula]
    ring
  rw [hremainder]
  exact log_stirlingSeq_sub_half_log_pi_bounds n hn

end Fabius
