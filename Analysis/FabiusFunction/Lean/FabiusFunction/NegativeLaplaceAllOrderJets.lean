import FabiusFunction.PeriodicSmooth
import FabiusFunction.LaplacePeriodicSecondOrder

/-!
# Exact all-order ordinary derivative jets

This module packages every ordinary derivative of the negative-Laplace
logarithm into a single recursive sequence.  On the positive half-line the
sequence agrees with `iteratedDeriv`; after dyadic rescaling, each derivative
splits exactly into a linear drift, a smooth periodic jet, and a forward-tail
remainder.
-/

set_option autoImplicit false

open Filter Set

namespace Fabius

/-- Explicit ordinary derivative sequence of the negative Laplace logarithm. -/
noncomputable def negativeLaplaceLogOrdinaryDeriv : ℕ → ℝ → ℝ
  | 0 => negativeLaplaceLog
  | n + 1 => fun s =>
      (negativeLaplaceJetSlope n * Real.logb 2 s +
          negativeLaplacePeriodicJet n (Real.logb 2 s)) /
        s ^ (n + 1) -
      negativeLaplaceForwardTailDeriv (n + 1) s

/-- The zeroth explicit ordinary derivative is the negative-Laplace logarithm. -/
@[simp] theorem negativeLaplaceLogOrdinaryDeriv_zero :
    negativeLaplaceLogOrdinaryDeriv 0 = negativeLaplaceLog := by
  rfl

/-- Unfolding equation for a positive-order ordinary derivative. -/
theorem negativeLaplaceLogOrdinaryDeriv_succ_apply
    (n : ℕ) (s : ℝ) :
    negativeLaplaceLogOrdinaryDeriv (n + 1) s =
      (negativeLaplaceJetSlope n * Real.logb 2 s +
          negativeLaplacePeriodicJet n (Real.logb 2 s)) /
        s ^ (n + 1) -
      negativeLaplaceForwardTailDeriv (n + 1) s := by
  rfl

private theorem logb_two_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Real.logb 2)
      ((1 / s) / Real.log 2) s := by
  unfold Real.logb
  simpa [one_div] using (Real.hasDerivAt_log hs.ne').div_const (Real.log 2)

private theorem negativeLaplacePeriodicJet_hasDerivAt
    (n : ℕ) (t : ℝ) :
    HasDerivAt (negativeLaplacePeriodicJet n)
      (deriv (negativeLaplacePeriodicJet n) t) t :=
  ((contDiff_infty_negativeLaplacePeriodicJet n).differentiable
    (by simp) t).hasDerivAt

/-- The explicit sequence is a genuine derivative tower on the positive
half-line. -/
theorem negativeLaplaceLogOrdinaryDeriv_hasDerivAt
    (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (negativeLaplaceLogOrdinaryDeriv n)
      (negativeLaplaceLogOrdinaryDeriv (n + 1) s) s := by
  cases n with
  | zero =>
      let F : BoundedFabius := Existence.boundedCandidate
      have hF : IsFabius F := Existence.boundedCandidate_isFabius
      have hq := negativeLaplaceLog_hasDerivAt F hF hs
      refine hq.congr_deriv ?_
      rw [negativeLaplaceLogFirst_eq_periodic F hF hs]
      have htail1 : negativeLaplaceForwardTailDeriv 1 s =
          negativeLaplaceForwardTailFirst s := by
        unfold negativeLaplaceForwardTailDeriv negativeLaplaceForwardTailFirst
        apply tsum_congr
        intro k
        exact negativeLaplaceForwardTermDeriv_one s k
      simp only [negativeLaplaceLogOrdinaryDeriv_succ_apply,
        negativeLaplaceJetSlope_zero,
        negativeLaplacePeriodicJet_zero, htail1]
      rw [show Real.log s = Real.log 2 * Real.logb 2 s by
        unfold Real.logb
        field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']]
      field_simp [hs.ne']
      ring
  | succ n =>
      let t := Real.logb 2 s
      let A : ℝ → ℝ := fun x =>
        negativeLaplaceJetSlope n * Real.logb 2 x +
          negativeLaplacePeriodicJet n (Real.logb 2 x)
      have hlogb := logb_two_hasDerivAt hs
      have hp := (negativeLaplacePeriodicJet_hasDerivAt n t).comp s hlogb
      have hA : HasDerivAt A
          (negativeLaplaceJetSlope n * ((1 / s) / Real.log 2) +
            deriv (negativeLaplacePeriodicJet n) t *
              ((1 / s) / Real.log 2)) s := by
        exact (hlogb.const_mul (negativeLaplaceJetSlope n)).add hp
      have hden : HasDerivAt (fun x : ℝ => x ^ (n + 1))
          ((n + 1 : ℝ) * s ^ n) s := by
        have hh := hasDerivAt_pow (n + 1) s
        simpa only [Nat.add_sub_cancel] using hh.congr_deriv (by
          push_cast
          rfl)
      have hdenne : s ^ (n + 1) ≠ 0 := pow_ne_zero _ hs.ne'
      have hquot := hA.div hden hdenne
      have htail := negativeLaplaceForwardTailDeriv_hasDerivAt
        (n + 1) s hs
      change HasDerivAt
        (fun x => A x / x ^ (n + 1) -
          negativeLaplaceForwardTailDeriv (n + 1) x)
        _ s
      refine (hquot.sub htail).congr_deriv ?_
      simp only [negativeLaplaceLogOrdinaryDeriv_succ_apply,
        negativeLaplacePeriodicJet]
      dsimp only [A, t]
      rw [negativeLaplaceJetSlope_succ]
      simp only [add_assoc]
      field_simp [hs.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
      ring

/-- `deriv` advances the explicit ordinary-derivative sequence at every
positive scale. -/
theorem deriv_negativeLaplaceLogOrdinaryDeriv
    (n : ℕ) {s : ℝ} (hs : 0 < s) :
    deriv (negativeLaplaceLogOrdinaryDeriv n) s =
      negativeLaplaceLogOrdinaryDeriv (n + 1) s :=
  (negativeLaplaceLogOrdinaryDeriv_hasDerivAt n hs).deriv

/-- Every member of the explicit derivative sequence is continuous on the
positive half-line. -/
theorem continuousOn_negativeLaplaceLogOrdinaryDeriv (n : ℕ) :
    ContinuousOn (negativeLaplaceLogOrdinaryDeriv n) (Ioi 0) := by
  intro s hs
  change 0 < s at hs
  exact (negativeLaplaceLogOrdinaryDeriv_hasDerivAt n hs).continuousAt.continuousWithinAt

/-- Every iterated derivative agrees pointwise with the explicit ordinary
derivative sequence at positive scales. -/
theorem iteratedDeriv_negativeLaplaceLog_eq_ordinaryDeriv
    (n : ℕ) {s : ℝ} (hs : 0 < s) :
    iteratedDeriv n negativeLaplaceLog s =
      negativeLaplaceLogOrdinaryDeriv n s := by
  induction n generalizing s with
  | zero => simp [negativeLaplaceLogOrdinaryDeriv]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n negativeLaplaceLog =ᶠ[nhds s]
          negativeLaplaceLogOrdinaryDeriv n := by
        filter_upwards [Ioi_mem_nhds hs] with x hx
        exact ih hx
      rw [heq.deriv_eq]
      exact (negativeLaplaceLogOrdinaryDeriv_hasDerivAt n hs).deriv

/-- Function-level form of the all-order derivative identification on the
positive half-line. -/
theorem iteratedDeriv_negativeLaplaceLog_eqOn_ordinaryDeriv (n : ℕ) :
    EqOn (iteratedDeriv n negativeLaplaceLog)
      (negativeLaplaceLogOrdinaryDeriv n) (Ioi 0) := by
  intro s hs
  change 0 < s at hs
  exact iteratedDeriv_negativeLaplaceLog_eq_ordinaryDeriv n hs

/-- Scaled `(n+1)`st ordinary derivative of the negative Laplace logarithm
on the dyadic logarithmic orbit. -/
noncomputable def negativeLaplaceScaledOrdinaryJet (n : ℕ) (t : ℝ) : ℝ :=
  ((2 : ℝ) ^ t) ^ (n + 1) *
    iteratedDeriv (n + 1) negativeLaplaceLog ((2 : ℝ) ^ t)

/-- Scaled forward-tail derivative removed from the exact ordinary jet. -/
noncomputable def negativeLaplaceForwardScaledJet (n : ℕ) (t : ℝ) : ℝ :=
  ((2 : ℝ) ^ t) ^ (n + 1) *
    negativeLaplaceForwardTailDeriv (n + 1) ((2 : ℝ) ^ t)

/-- Exact affine-periodic-plus-tail decomposition of every scaled ordinary
derivative jet. -/
theorem negativeLaplaceScaledOrdinaryJet_eq
    (n : ℕ) (t : ℝ) :
    negativeLaplaceScaledOrdinaryJet n t =
      negativeLaplaceJetSlope n * t +
        negativeLaplacePeriodicJet n t -
          negativeLaplaceForwardScaledJet n t := by
  rw [negativeLaplaceScaledOrdinaryJet,
    iteratedDeriv_negativeLaplaceLog_eq_ordinaryDeriv (n + 1)
      (Real.rpow_pos_of_pos (by norm_num) t),
    negativeLaplaceLogOrdinaryDeriv_succ_apply]
  have hlogb : Real.logb 2 ((2 : ℝ) ^ t) = t := by
    rw [Real.logb_rpow (by norm_num)]
    norm_num
  rw [hlogb]
  unfold negativeLaplaceForwardScaledJet
  have hpow : ((2 : ℝ) ^ t) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (by positivity)
  field_simp [hpow]

/-- Adding back the scaled forward tail leaves exactly the affine-periodic
part of the ordinary derivative jet. -/
theorem negativeLaplaceScaledOrdinaryJet_add_forwardScaledJet
    (n : ℕ) (t : ℝ) :
    negativeLaplaceScaledOrdinaryJet n t +
        negativeLaplaceForwardScaledJet n t =
      negativeLaplaceJetSlope n * t + negativeLaplacePeriodicJet n t := by
  rw [negativeLaplaceScaledOrdinaryJet_eq]
  ring

end Fabius
