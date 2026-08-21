import ExponentialIdentities.TwoBaseIntegerExponent.ZeroDensity

/-!
# Sharp three-term progression obstructions

The Roth-density development uses the convenient sufficient condition `h ^ 5 ≤ n` to
exclude three two-base candidates in an arithmetic progression.  The underlying curvature
estimate proves the sharper natural condition directly:

`alpha * (alpha - 1) * h ^ 2 < n ^ (2 - alpha)`,

where `alpha = log 3 / log 2`.  This file records that stronger conclusion without replacing
the real exponent `2 - alpha` by a coarser integral power.
-/

namespace LeanProofs.TwoBaseIntegerExponent

/-- Under the sharp curvature inequality, the step-`h` second difference of
`m ↦ m ^ (log 3 / log 2)` lies strictly between zero and one. -/
theorem second_difference_logThreeDivLogTwo_ap_of_curvature
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      logThreeDivLogTwo * (logThreeDivLogTwo - 1) * (h : ℝ) ^ 2 <
        (n : ℝ) ^ (2 - logThreeDivLogTwo)) :
    0 < ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo ∧
      ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo -
          2 * ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo +
          (n : ℝ) ^ logThreeDivLogTwo < 1 := by
  obtain ⟨hpos, hbound⟩ :=
    second_difference_logThreeDivLogTwo_ap_bound n h hn hh
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpowpos : 0 < (n : ℝ) ^ (logThreeDivLogTwo - 2) :=
    Real.rpow_pos_of_pos hnpos _
  have hmul :
      logThreeDivLogTwo * (logThreeDivLogTwo - 1) * (h : ℝ) ^ 2 *
          (n : ℝ) ^ (logThreeDivLogTwo - 2) <
        (n : ℝ) ^ (2 - logThreeDivLogTwo) *
          (n : ℝ) ^ (logThreeDivLogTwo - 2) :=
    mul_lt_mul_of_pos_right hcurv hpowpos
  have hcancel :
      (n : ℝ) ^ (2 - logThreeDivLogTwo) *
          (n : ℝ) ^ (logThreeDivLogTwo - 2) = 1 := by
    rw [← Real.rpow_add hnpos]
    norm_num
  exact ⟨hpos, hbound.trans (hmul.trans_eq hcancel)⟩

/-- Three integral values of `m ↦ m ^ (log 3 / log 2)` cannot occur in an arithmetic
progression whenever the exact curvature upper bound is less than one. -/
theorem not_three_arithmetic_progression_logThreeDivLogTwo_rpow_integers_of_curvature
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      logThreeDivLogTwo * (logThreeDivLogTwo - 1) * (h : ℝ) ^ 2 <
        (n : ℝ) ^ (2 - logThreeDivLogTwo))
    (h₀ : ∃ z : ℤ, (z : ℝ) = (n : ℝ) ^ logThreeDivLogTwo)
    (h₁ : ∃ z : ℤ, (z : ℝ) = ((n + h : ℕ) : ℝ) ^ logThreeDivLogTwo)
    (h₂ : ∃ z : ℤ, (z : ℝ) = ((n + 2 * h : ℕ) : ℝ) ^ logThreeDivLogTwo) :
    False := by
  obtain ⟨z₀, hz₀⟩ := h₀
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₂, hz₂⟩ := h₂
  obtain ⟨hpos, hlt⟩ :=
    second_difference_logThreeDivLogTwo_ap_of_curvature n h hn hh hcurv
  have hzpos : (0 : ℤ) < z₂ - 2 * z₁ + z₀ := by
    exact_mod_cast (show (0 : ℝ) <
      (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) by
        rw [hz₂, hz₁, hz₀]
        exact hpos)
  have hzlt : z₂ - 2 * z₁ + z₀ < (1 : ℤ) := by
    exact_mod_cast (show
      (z₂ : ℝ) - 2 * (z₁ : ℝ) + (z₀ : ℝ) < 1 by
        rw [hz₂, hz₁, hz₀]
        exact hlt)
  omega

/-- Sharp arithmetic-progression obstruction stated directly for natural two-base
candidates.  This strictly refines the earlier sufficient hypothesis `h ^ 5 ≤ n`. -/
theorem not_three_arithmetic_progression_twoBaseNaturalCandidates_of_curvature
    (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hcurv :
      logThreeDivLogTwo * (logThreeDivLogTwo - 1) * (h : ℝ) ^ 2 <
        (n : ℝ) ^ (2 - logThreeDivLogTwo)) :
    ¬(TwoBaseNaturalCandidate n ∧
      TwoBaseNaturalCandidate (n + h) ∧
      TwoBaseNaturalCandidate (n + 2 * h)) := by
  rintro ⟨h₀, h₁, h₂⟩
  exact
    not_three_arithmetic_progression_logThreeDivLogTwo_rpow_integers_of_curvature
      n h hn hh hcurv h₀.2 h₁.2 h₂.2

end LeanProofs.TwoBaseIntegerExponent
