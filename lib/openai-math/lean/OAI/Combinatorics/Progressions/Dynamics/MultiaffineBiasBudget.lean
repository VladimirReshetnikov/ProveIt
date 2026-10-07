import OAI.Combinatorics.Progressions.Estimates.ProductDifferenceBias

namespace OAI

section

namespace Erdos3

noncomputable def multiaffineBiasBudget (n : ℕ) (ζ : ℝ) : ℝ :=
  denseProductDensityBudget n (ζ^(2^n)/(2*3^n))/ζ^(2^n)

theorem multiaffineBiasBudget_pos (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    0 < multiaffineBiasBudget n ζ := by
  have h := denseProductDensityBudget_pos n
    (show 0 < ζ^(2^n)/(2*3^n) by positivity)
  exact div_pos h (pow_pos hζ _)

theorem multiaffineBiasBudget_bounds (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) ≤ multiaffineBiasBudget n ζ ∧
    multiaffineBiasBudget n ζ * ζ^(2^n) = denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) := by
  have hp : 0 < ζ^(2^n) := pow_pos hζ _
  have hp1 : ζ^(2^n) ≤ 1 := pow_le_one₀ hζ.le hζ1
  have hL := denseProductDensityBudget_pos n
    (show 0 < ζ^(2^n)/(2*3^n) by positivity)
  constructor
  · apply (le_div_iff₀ hp).mpr
    exact mul_le_of_le_one_right hL.le hp1
  · exact div_mul_cancel₀ _ hp.ne'

theorem multiaffineBiasBudget_eq_power (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget n ζ =
      ((denseProductDensityConstant n : ℝ)*(2*3^n)^denseProductExponent n) /
        ζ^(2^n*(denseProductExponent n+1)) := by
  unfold multiaffineBiasBudget denseProductDensityBudget
  rw [div_pow, div_div, mul_add, mul_one, pow_add, pow_mul]
  field_simp

end Erdos3

end

end OAI
