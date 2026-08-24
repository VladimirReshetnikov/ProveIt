import FabiusFunction.PeriodicSmooth
import FabiusFunction.LaplacePeriodicSecondOrder

/-! Exact all-order ordinary derivative jets of the negative Laplace logarithm. -/

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

@[simp] theorem negativeLaplaceLogOrdinaryDeriv_zero :
    negativeLaplaceLogOrdinaryDeriv 0 = negativeLaplaceLog := by
  rfl

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

/-- Scaled `(n+1)`st ordinary derivative of the negative Laplace logarithm
on the dyadic logarithmic orbit. -/
noncomputable def negativeLaplaceScaledOrdinaryJet (n : ℕ) (t : ℝ) : ℝ :=
  ((2 : ℝ) ^ t) ^ (n + 1) *
    iteratedDeriv (n + 1) negativeLaplaceLog ((2 : ℝ) ^ t)

/-- Scaled forward-tail derivative removed from the exact ordinary jet. -/
noncomputable def negativeLaplaceForwardScaledJet (n : ℕ) (t : ℝ) : ℝ :=
  ((2 : ℝ) ^ t) ^ (n + 1) *
    negativeLaplaceForwardTailDeriv (n + 1) ((2 : ℝ) ^ t)

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

end Fabius
