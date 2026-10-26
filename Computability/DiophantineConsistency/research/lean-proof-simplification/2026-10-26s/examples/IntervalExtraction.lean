import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace NewSimplifications

/-- Two certificates identify the same integer unit interval. The second
certificate may use a separate approximation error and a ratio error. -/
theorem integer_of_error_budget {Y t : ℕ} {ρ δ ε : ℝ}
    (hδ : 0 ≤ δ) (hbudget : δ + ε ≤ 1)
    (hYlow : (Y : ℝ) < ρ) (hYhigh : ρ < Y + 1)
    (htlow : (t : ℝ) + δ < ρ) (hthigh : ρ < t + δ + ε) : Y = t := by
  have hρ : 0 ≤ ρ := (Nat.cast_nonneg Y).trans hYlow.le
  have hY : Nat.floor ρ = Y := (Nat.floor_eq_iff hρ).mpr ⟨hYlow.le, hYhigh⟩
  have ht : Nat.floor ρ = t := (Nat.floor_eq_iff hρ).mpr ⟨by linarith, by linarith⟩
  exact hY.symm.trans ht

/-- The rounding step of NativeHalfBinomial.half_binomial_of_ratio, after
its existing central-binomial parity argument and real decomposition. -/
theorem native_half_binomial_rounding {Y t : ℕ} {ρ f : ℝ}
    (hf0 : 0 ≤ f) (hf1 : f < 1)
    (hYlow : (Y : ℝ) < ρ) (hYhigh : ρ < Y + 1)
    (hlow : (t : ℝ) + f / 2 < ρ)
    (hhigh : ρ < t + f / 2 + 1 / 2) : t = Y := by
  exact (integer_of_error_budget (by positivity) (by linarith)
    hYlow hYhigh hlow hhigh).symm

/-- The rounding step of Jones1980.Ratio90.Y_eq_floor, after the established
binomial decomposition with remainder < 1/4 and ratio error < 1/2. -/
theorem ordinary_binomial_rounding {Y F : ℕ} {ρ δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδlt : δ < 1 / 4)
    (hYlow : (Y : ℝ) < ρ) (hYhigh : ρ < Y + 1)
    (hlow : (F : ℝ) + δ < ρ)
    (hhigh : ρ < F + δ + 1 / 2) : Y = F := by
  exact integer_of_error_budget hδ0 (by linarith) hYlow hYhigh hlow hhigh

/-- A variable positive denominator exposes exactly which scaling remains
safe: the sum of the fractional and ratio errors is at most one. -/
theorem scaled_rounding {Y t : ℕ} {ρ f s : ℝ}
    (hs : 2 ≤ s) (hf0 : 0 ≤ f) (hf1 : f < 1)
    (hYlow : (Y : ℝ) < ρ) (hYhigh : ρ < Y + 1)
    (hlow : (t : ℝ) + f / s < ρ)
    (hhigh : ρ < t + f / s + 1 / s) : Y = t := by
  apply integer_of_error_budget (div_nonneg hf0 (by linarith)) ?_ hYlow hYhigh hlow hhigh
  rw [← add_div, div_le_iff₀ (by linarith : 0 < s)]
  linarith

#print axioms integer_of_error_budget
#print axioms native_half_binomial_rounding
#print axioms ordinary_binomial_rounding
#print axioms scaled_rounding
end NewSimplifications
