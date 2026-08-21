import ExponentialIdentities.TwoBaseIntegerExponent.ZeroDensity

/-!
# A sharper three-term progression obstruction

The committed obstruction forbids three candidates in arithmetic progression under the
hypothesis `h ^ 5 ≤ n`, i.e. step exponent `1/5 = 0.2`.  The curvature bound behind it,
`0 < Δ² < θ(θ-1)·h²·nᶿ⁻²` with `θ = log 3 / log 2`, supports the sharp step exponent
`(2-θ)/2 = 0.20751…`.  This file realizes almost all of that gain with the rational
hypothesis
\[
  h^{400} \le n^{83},
\]
i.e. step exponent `83/400 = 0.2075`.  The two numerical ingredients are the enclosure
`θ < 317/200` (from the exact power inequality `3^200 < 2^317`, replayed by the kernel) and
the resulting bound `θ(θ-1) < 37089/40000 < 1`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

set_option exponentiation.threshold 400 in
private theorem three_pow_200_lt_two_pow_317 : 3 ^ 200 < 2 ^ 317 := by norm_num

/-- The sharp rational upper enclosure `θ < 317/200 = 1.585` for `θ = log 3 / log 2`. -/
theorem logThreeDivLogTwo_lt_317_div_200 :
    logThreeDivLogTwo < (317 / 200 : ℝ) := by
  rw [logThreeDivLogTwo, div_lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (by norm_num : (0 : ℝ) < 200)]
  have hpow : ((3 : ℝ) ^ (200 : ℕ)) < ((2 : ℝ) ^ (317 : ℕ)) := by
    exact_mod_cast three_pow_200_lt_two_pow_317
  have hlog := Real.strictMonoOn_log
    (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < (3 : ℝ) ^ (200 : ℕ) by positivity))
    (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < (2 : ℝ) ^ (317 : ℕ) by positivity))
    hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

private theorem theta_mul_theta_sub_one_lt :
    logThreeDivLogTwo * (logThreeDivLogTwo - 1) < (37089 / 40000 : ℝ) := by
  have h1 := one_lt_logThreeDivLogTwo
  have h2 := logThreeDivLogTwo_lt_317_div_200
  nlinarith [mul_pos (sub_pos.mpr h2)
    (show (0 : ℝ) < logThreeDivLogTwo + 317 / 200 - 1 by linarith)]

/-- Under `h ^ 400 ≤ n ^ 83` the step-`h` second difference lies strictly between zero and
one. -/
theorem second_difference_logThreeDivLogTwo_ap_sharp
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hscale : h ^ 400 ≤ n ^ 83) :
    0 < ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo ∧
      ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo < 1 := by
  obtain ⟨hpos, hbound⟩ := second_difference_logThreeDivLogTwo_ap_bound n h hn hh
  refine ⟨hpos, hbound.trans ?_⟩
  -- It remains to bound `θ(θ-1) * h² * n^(θ-2)` by `1`.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhpos : (0 : ℝ) < h := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hh
  -- Step 1: `n^(θ-2) ≤ n^(-(83/200))`.
  have hexp : logThreeDivLogTwo - 2 ≤ -(83 / 200 : ℝ) := by
    linarith [logThreeDivLogTwo_lt_317_div_200]
  have hstep1 : (n : ℝ) ^ (logThreeDivLogTwo - 2) ≤ (n : ℝ) ^ (-(83 / 200 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hexp
  -- Step 2: `h² ≤ n^(83/200)` from the natural hypothesis, via `t ↦ t^(1/200)`.
  have hcast : ((h : ℝ) ^ (400 : ℕ)) ≤ ((n : ℝ) ^ (83 : ℕ)) := by exact_mod_cast hscale
  have hstep2 : ((h : ℝ)) ^ (2 : ℕ) ≤ (n : ℝ) ^ ((83 : ℝ) / 200) := by
    have hmono := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (h : ℝ) ^ (400 : ℕ)) hcast
      (by norm_num : (0 : ℝ) ≤ (200 : ℝ)⁻¹)
    rw [← Real.rpow_natCast (h : ℝ) 400, ← Real.rpow_natCast (n : ℝ) 83,
      ← Real.rpow_mul hhpos.le, ← Real.rpow_mul hnpos.le] at hmono
    norm_num at hmono
    exact hmono
  -- Step 3: combine.
  have hsize : (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2) ≤ 1 := by
    have hnneg : (0 : ℝ) < (n : ℝ) ^ ((83 : ℝ) / 200) := Real.rpow_pos_of_pos hnpos _
    have hneg : (n : ℝ) ^ (-(83 / 200 : ℝ)) = ((n : ℝ) ^ ((83 : ℝ) / 200))⁻¹ :=
      Real.rpow_neg hnpos.le _
    calc (h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2)
        ≤ (h : ℝ) ^ 2 * (n : ℝ) ^ (-(83 / 200 : ℝ)) := by gcongr
      _ = (h : ℝ) ^ 2 / (n : ℝ) ^ ((83 : ℝ) / 200) := by
          rw [hneg]
          ring
      _ ≤ 1 := by
          rw [div_le_one hnneg]
          exact hstep2
  have hθpos : 0 < logThreeDivLogTwo * (logThreeDivLogTwo - 1) := by
    have h1 := one_lt_logThreeDivLogTwo
    nlinarith
  calc logThreeDivLogTwo * (logThreeDivLogTwo - 1) * (h : ℝ) ^ 2 *
        (n : ℝ) ^ (logThreeDivLogTwo - 2)
      = logThreeDivLogTwo * (logThreeDivLogTwo - 1) *
        ((h : ℝ) ^ 2 * (n : ℝ) ^ (logThreeDivLogTwo - 2)) := by ring
    _ ≤ logThreeDivLogTwo * (logThreeDivLogTwo - 1) * 1 :=
        mul_le_mul_of_nonneg_left hsize hθpos.le
    _ < 1 := by
        have := theta_mul_theta_sub_one_lt
        linarith

/-- **Sharp three-term progression obstruction.**  Three integral candidate values cannot
occur in an arithmetic progression of step `h` once `h ^ 400 ≤ n ^ 83`, i.e. up to step
`h ≈ n^{0.2075}`, essentially the optimal exponent `(2-θ)/2 = 0.20751…` of the curvature
method; the committed criterion `h ^ 5 ≤ n` corresponds to the strictly smaller exponent
`0.2`. -/
theorem not_three_arithmetic_progression_twoBaseNaturalCandidates_sharp
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hscale : h ^ 400 ≤ n ^ 83) :
    ¬(TwoBaseNaturalCandidate n ∧
      TwoBaseNaturalCandidate (n + h) ∧
      TwoBaseNaturalCandidate (n + 2 * h)) := by
  rintro ⟨h₀, h₁, h₂⟩
  obtain ⟨z₀, hz₀⟩ := h₀.2
  obtain ⟨z₁, hz₁⟩ := h₁.2
  obtain ⟨z₂, hz₂⟩ := h₂.2
  obtain ⟨hpos, hlt⟩ := second_difference_logThreeDivLogTwo_ap_sharp n h hn hh hscale
  have hzpos : (0 : ℤ) < z₂ - 2 * z₁ + z₀ := by
    exact_mod_cast (show (0 : ℝ) < (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) by
      rw [hz₂, hz₁, hz₀]
      exact hpos)
  have hzlt : z₂ - 2 * z₁ + z₀ < (1 : ℤ) := by
    exact_mod_cast (show (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) < 1 by
      rw [hz₂, hz₁, hz₀]
      exact hlt)
  omega

end LeanProofs.TwoBaseIntegerExponent
