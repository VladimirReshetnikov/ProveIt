import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace LeanProofs.TwoBaseIntegerExponent

/-- The normalized local-minus-endpoint rate at compound level `rho` is
uniformly negative whenever the cheaper endpoint logarithm is `l₂` and the
more expensive one is `l₃`.  This is the algebraic core of the cross-
Sylvester compound no-closure calculation. -/
theorem compoundEndpointRate_le_neg_l₂
    (ρ l₂ l₃ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hl₂0 : 0 ≤ l₂) (hl₂₃ : l₂ ≤ l₃) :
    ρ ^ 3 / 2 * (l₂ + l₃) - l₂ - ρ * l₃ ≤ -l₂ := by
  have h1mρ : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ1
  have h1pρ : 0 ≤ 1 + ρ := by linarith
  have hfac : 0 ≤ ρ * (1 - ρ) * (1 + ρ) :=
    mul_nonneg (mul_nonneg hρ0 h1mρ) h1pρ
  have hρ3 : ρ ^ 3 ≤ ρ := by
    nlinarith
  have hρ3nonneg : 0 ≤ ρ ^ 3 := by positivity
  have hl₃0 : 0 ≤ l₃ := hl₂0.trans hl₂₃
  have hmean : (l₂ + l₃) / 2 ≤ l₃ := by linarith
  have hleft : ρ ^ 3 * ((l₂ + l₃) / 2) ≤ ρ ^ 3 * l₃ :=
    mul_le_mul_of_nonneg_left hmean hρ3nonneg
  have hright : ρ ^ 3 * l₃ ≤ ρ * l₃ :=
    mul_le_mul_of_nonneg_right hρ3 hl₃0
  calc
    ρ ^ 3 / 2 * (l₂ + l₃) - l₂ - ρ * l₃
        = ρ ^ 3 * ((l₂ + l₃) / 2) - l₂ - ρ * l₃ := by ring
    _ ≤ ρ * l₃ - l₂ - ρ * l₃ := by linarith
    _ = -l₂ := by ring

/-- Specialization to the structural endpoint bases 2 and 3. -/
theorem crossCompoundEndpointRate_le_neg_log_two
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ 3 / 2 * Real.log 6 - Real.log 2 - ρ * Real.log 3
      ≤ -Real.log 2 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog23 : Real.log 2 ≤ Real.log 3 := by
    exact (Real.strictMonoOn_log.monotoneOn
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (3 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2 : ℝ) ≤ 3))
  have h := compoundEndpointRate_le_neg_l₂
    ρ (Real.log 2) (Real.log 3) hρ0 hρ1 hlog2 hlog23
  rw [show Real.log 6 = Real.log 2 + Real.log 3 by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]]
  exact h


end LeanProofs.TwoBaseIntegerExponent
