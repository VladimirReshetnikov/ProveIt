import OAI.Combinatorics.Progressions.Estimates.IndependentReturnScale
import OAI.Combinatorics.Progressions.Fourier.UnbalancedBohrShape

namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalanced_power_gap {c : ℝ} (hc : 0 < c) {q : ℕ} (hq : 0 < q) :
    c / 2 ≤ (1 + c) ^ q - (1 + c / 2) ^ q := by
  have h : ∀ n : ℕ, c / 2 ≤ (1 + c) ^ (n + 1) - (1 + c / 2) ^ (n + 1) := by
    intro n
    induction n with
    | zero => norm_num; linarith
    | succ n ih =>
      have hd : 0 ≤ (1 + c) ^ (n + 1) - (1 + c / 2) ^ (n + 1) := by linarith
      have hb : 0 ≤ (1 + c / 2) ^ (n + 1) := pow_nonneg (by linarith) _
      have hmul := mul_nonneg hc.le hd
      have hmul' := mul_nonneg hc.le hb
      change c / 2 ≤ (1 + c) ^ ((n + 1) + 1) - (1 + c / 2) ^ ((n + 1) + 1)
      rw [pow_succ (1 + c) (n + 1), pow_succ (1 + c / 2) (n + 1)]
      nlinarith
  cases q with
  | zero => omega
  | succ n => exact h n

noncomputable def unbalancedErrorBudget (c : ℝ) : ℝ := -Real.log (c / 32)

theorem unbalancedErrorBudget_spec {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ unbalancedErrorBudget c ∧ Real.exp (-unbalancedErrorBudget c) / 2 = c / 64 := by
  constructor
  · unfold unbalancedErrorBudget
    apply neg_nonneg.mpr
    exact Real.log_nonpos (by positivity) (by linarith)
  · unfold unbalancedErrorBudget
    rw [neg_neg, Real.exp_log (by positivity)]
    ring

noncomputable def unbalancedWidthLoss (rank : ℕ) (c p H : ℝ) : ℝ :=
  ((rank : ℝ) + 2 * H * p ^ 2 + unbalancedErrorBudget c + 1600) +
    (((rank + unbalancedRankExtra c p H : ℕ) : ℝ) + 2 * p + unbalancedErrorBudget c + 1600) +
    8 + almostPeriodicityWidthConstant (c / 64) *
      (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + rank))

theorem unbalancedMinimumWidth_exp_lower {N : ℕ} [NeZero N]
    (S : CyclicBohr.Set N) {M c p H : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hcap : M ≤ Real.exp p) {q : ℕ} (hq : 0 < q) (hqp : (q : ℝ) ≤ H * p) :
    S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H) ≤
      unbalancedMinimumWidth S M c p H q := by
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨hE, hEeq⟩ := unbalancedErrorBudget_spec hc hc1
  have hMpow : M ^ (2 * q) ≤ Real.exp (2 * H * p ^ 2) := by
    calc
      _ ≤ (Real.exp p) ^ (2 * q) := pow_le_pow_left₀ hM hcap _
      _ = Real.exp (((2 * q : ℕ) : ℝ) * p) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hqp hp0]
  have hMtwo : M ^ 2 ≤ Real.exp (2 * p) := by
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ hM hcap _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have heps : Real.exp (-unbalancedErrorBudget c) / 2 ≤
      (1 + c) ^ q - (1 + c / 2) ^ q := by
    rw [hEeq]
    exact (show c / 64 ≤ c / 2 by linarith).trans (unbalanced_power_gap hc hq)
  have hκ := localizedAverageScale_exp_lower_of_error S.rank (pow_nonneg hM (2 * q))
    hMpow (by positivity : 0 ≤ 2 * H * p ^ 2) hE heps
  have hσ := localizedAverageScale_exp_lower_of_error (S.rank + unbalancedRankExtra c p H)
    (sq_nonneg M) hMtwo (by positivity : 0 ≤ 2 * p) hE hEeq.le
  have h8 : Real.exp (-8 : ℝ) ≤ 1 / 8 := by
    have h : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp 8]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  let a := (S.rank : ℝ) + 2 * H * p ^ 2 + unbalancedErrorBudget c + 1600
  let b := ((S.rank + unbalancedRankExtra c p H : ℕ) : ℝ) + 2 * p + unbalancedErrorBudget c + 1600
  let t := almostPeriodicityWidthConstant (c / 64) *
    (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + S.rank))
  have hSnonneg := S.radius_nonneg
  have hexp : Real.exp (-(a + b + 8 + t)) =
      Real.exp (-a) * Real.exp (-b) * Real.exp (-8) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change S.radius * Real.exp (-(a + b + 8 + t)) ≤ _
  calc
    _ = Real.exp (-a) * Real.exp (-b) * S.radius * Real.exp (-8) * Real.exp (-t) := by
      rw [hexp]
      ring
    _ ≤ (localizedAverageScale S.rank (M ^ (2 * q)) ((1 + c) ^ q - (1 + c / 2) ^ q) : ℝ) *
        (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) *
        S.radius * (1 / 8) * Real.exp (-t) := by gcongr
    _ = _ := by unfold unbalancedMinimumWidth; dsimp only [t]; ring

end Erdos3.LocalConvolution

end

end OAI
