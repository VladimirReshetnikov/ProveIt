import FabiusFunction.LaplacePeriodicSecondOrder
import FabiusFunction.FabiusLambertPhase

/-!
# Sharp dyadic Fabius asymptotic at the exact Lambert phase

The endpoint cumulant expansion contains a derivative of the periodic
negative-Laplace correction at `logb 2 n`.  The refined lower-Lambert expansion
shows that this is precisely the first-order displacement of the periodic
correction from `logb 2 n` to its exact saddle phase.

This module performs that Taylor transfer with a uniform quadratic remainder
and proves the unconditional corrected dyadic formula with error `O(1/n)`.
Keeping the exact lower-Lambert phase is essential: replacing it merely by
`logb 2 n` would leave a generally larger `log n / n` term.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- First displacement term in the lower-Lambert phase. -/
noncomputable def dyadicPeriodicPhaseShift (n : ℕ) : ℝ :=
  Real.log (n : ℝ) / (Real.log 2) ^ 2 / (n : ℝ)

/-- The first phase displacement is normalized to zero at `n = 0`. -/
@[simp] theorem dyadicPeriodicPhaseShift_zero :
    dyadicPeriodicPhaseShift 0 = 0 := by
  simp [dyadicPeriodicPhaseShift]

/-- The refined lower-Lambert remainder remains `O(1/n)` after sampling on
the natural scales. -/
theorem dyadicLambertRefinedRemainder_nat_isBigO :
    (fun n : ℕ => dyadicLambertRefinedRemainder (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  simpa [Function.comp_def, one_div] using
    dyadicLambertRefinedRemainder_isBigO.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))

private lemma dyadicPeriodicPhaseShift_sq_isBigO_inv :
    (fun n : ℕ => dyadicPeriodicPhaseShift n ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have h := (log_pow_div_sq_isBigO_inv_nat 2).const_mul_left
    ((Real.log 2) ^ 4)⁻¹
  apply h.congr'
  · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    unfold dyadicPeriodicPhaseShift
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hn0]
  · exact Filter.EventuallyEq.rfl

private lemma inv_sq_isBigO_inv_nat :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 0 ≤ (n : ℝ)⁻¹ := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg hinv]
  nlinarith [inv_le_one_of_one_le₀ hn1]

/-- The first periodic phase displacement is bounded by `log n / n`. -/
theorem dyadicPeriodicPhaseShift_isBigO_log_div :
    dyadicPeriodicPhaseShift =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) := by
  have h := (isBigO_refl (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop)
    |>.const_mul_left ((Real.log 2) ^ 2)⁻¹
  apply h.congr'
  · filter_upwards with n
    unfold dyadicPeriodicPhaseShift
    ring
  · exact Filter.EventuallyEq.rfl

private lemma dyadicPeriodicPhaseShift_mul_refined_isBigO_inv :
    (fun n : ℕ => dyadicPeriodicPhaseShift n *
      dyadicLambertRefinedRemainder (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hraw := dyadicPeriodicPhaseShift_isBigO_log_div.mul
    dyadicLambertRefinedRemainder_nat_isBigO
  have htarget := log_pow_div_sq_isBigO_inv_nat 1
  exact hraw.trans <| htarget.congr_left (by
    intro n
    simp only [div_eq_mul_inv]
    ring)

/-- The square of the full lower-Lambert phase displacement is `O(1/n)` on
natural scales. -/
theorem dyadicLambertRemainder_sq_isBigO_inv_nat :
    (fun n : ℕ => dyadicLambertRemainder (n : ℝ) ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hE2 := dyadicLambertRefinedRemainder_nat_isBigO.pow 2 |>.trans
    inv_sq_isBigO_inv_nat
  have hsum := dyadicPeriodicPhaseShift_sq_isBigO_inv.add
    (dyadicPeriodicPhaseShift_mul_refined_isBigO_inv.const_mul_left 2) |>.add hE2
  apply hsum.congr'
  · filter_upwards with n
    unfold dyadicLambertRefinedRemainder
    unfold dyadicPeriodicPhaseShift
    ring
  · exact Filter.EventuallyEq.rfl

private lemma negativeLaplacePsi_lambert_eq_shifted (n : ℕ) :
    negativeLaplacePsi (dyadicLambertPhase (n : ℝ)) =
      negativeLaplacePsi
        (Real.logb 2 n + dyadicLambertRemainder (n : ℝ)) := by
  have hp : Function.Periodic negativeLaplacePsi 1 :=
    negativeLaplacePsi_add_one
  have hperiod := hp.sub_nat_mul_eq n (x := dyadicLambertPhase (n : ℝ))
  rw [← hperiod]
  congr 1
  unfold dyadicLambertRemainder Real.logb
  ring

/-- Sampling the periodic correction at the exact lower-Lambert phase equals
its value and first derivative at `logb 2 n`, up to `O(1/n)`. -/
theorem negativeLaplacePsi_dyadicLambert_sub_linear_isBigO :
    (fun n : ℕ =>
      negativeLaplacePsi (dyadicLambertPhase (n : ℝ)) -
        (negativeLaplacePsi (Real.logb 2 n) +
          dyadicPeriodicPhaseShift n *
            deriv negativeLaplacePsi (Real.logb 2 n))) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  rcases exists_negativeLaplacePsi_first_order_remainder_bound with
    ⟨C, _hC0, hC⟩
  let R : ℕ → ℝ := fun n => dyadicLambertRemainder (n : ℝ)
  let E : ℕ → ℝ := fun n => dyadicLambertRefinedRemainder (n : ℝ)
  let D : ℕ → ℝ := fun n => deriv negativeLaplacePsi (Real.logb 2 n)
  let T : ℕ → ℝ := fun n =>
    negativeLaplacePsi (Real.logb 2 n + R n) -
      negativeLaplacePsi (Real.logb 2 n) - D n * R n
  have hT : T =O[atTop] (fun n : ℕ => R n ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards with n
    change |T n| ≤ C * |R n ^ 2|
    have hR2 : |R n ^ 2| = R n ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [hR2]
    simpa [T, D, R, mul_comm] using hC (Real.logb 2 n) (R n)
  have hT' : T =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) :=
    hT.trans (by simpa [R] using dyadicLambertRemainder_sq_isBigO_inv_nat)
  have hD : D =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    simpa [D] using deriv_negativeLaplacePsi_logb_isBigO_one_nat
  have hE : E =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa [E] using dyadicLambertRefinedRemainder_nat_isBigO
  have hDE : (fun n => D n * E n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa using hD.mul hE
  have hsum := hT'.add hDE
  apply hsum.congr'
  · filter_upwards with n
    rw [negativeLaplacePsi_lambert_eq_shifted]
    dsimp [T, D, E, R]
    unfold dyadicLambertRefinedRemainder
    unfold dyadicPeriodicPhaseShift
    ring
  · exact Filter.EventuallyEq.rfl

/-- The corrected sharp dyadic main term, sampled at its exact Lambert phase. -/
noncomputable def dyadicSharpLambertMain (n : ℕ) : ℝ :=
  dyadicSharpElementaryMain n + fabiusSharpAsymptoticConstant -
    Real.log (n : ℝ) ^ 2 /
      (2 * (Real.log 2) ^ 2 * (n : ℝ)) +
    negativeLaplacePsi (dyadicLambertPhase (n : ℝ))

/-- Unconditional corrected sharp asymptotic for `F(2⁻ⁿ)`, with exact
lower-Lambert periodic phase and error `O(1/n)`. -/
theorem log_fabius_dyadic_sub_lambertMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ =>
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpLambertMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have h := (log_fabius_dyadic_sub_periodicDerivativeMain_isBigO F hF).sub
    negativeLaplacePsi_dyadicLambert_sub_linear_isBigO
  apply h.congr'
  · filter_upwards with n
    unfold dyadicSharpPeriodicDerivativeMain dyadicSharpLambertMain
    unfold dyadicPeriodicPhaseShift
    ring
  · exact Filter.EventuallyEq.rfl

end Fabius
