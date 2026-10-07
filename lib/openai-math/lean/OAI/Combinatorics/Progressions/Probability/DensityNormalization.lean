import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem density_lower_bound_of_log_inverse {alpha p : ℝ} (halpha : 0 < alpha)
    (hlog : Real.log (1 / alpha) ≤ p) : Real.exp (-p) ≤ alpha := by
  have he : Real.log alpha ≥ -p := by
    rw [Real.log_div (by norm_num) halpha.ne', Real.log_one, zero_sub] at hlog
    linarith
  calc
    _ ≤ Real.exp (Real.log alpha) := Real.exp_le_exp.mpr he
    _ = alpha := Real.exp_log halpha

theorem normalized_density_bounds {X : Type*} (f : X → ℝ) {alpha p : ℝ}
    (halpha : 0 < alpha) (hlower : Real.exp (-p) ≤ alpha)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : X) :
    0 ≤ f x / alpha ∧ f x / alpha ≤ Real.exp p := by
  refine ⟨div_nonneg (hf x).1 halpha.le, ?_⟩
  apply (div_le_iff₀ halpha).mpr
  calc
    f x ≤ 1 := (hf x).2
    _ = Real.exp p * Real.exp (-p) := by rw [← Real.exp_add]; simp
    _ ≤ Real.exp p * alpha := mul_le_mul_of_nonneg_left hlower (Real.exp_pos p).le

theorem normalized_density_mean {X : Type*} [Fintype X] (f : X → ℝ) {alpha : ℝ}
    (halpha : 0 < alpha) (hmean : (𝔼 x, f x) = alpha) :
    (𝔼 x, f x / alpha) = 1 := by
  rw [← Finset.expect_div, hmean, div_self halpha.ne']

theorem support_normalized_density {X : Type*} (f : X → ℝ) {alpha : ℝ}
    (halpha : alpha ≠ 0) : Function.support (fun x => f x / alpha) = Function.support f := by
  ext x
  simp [Function.mem_support, halpha]

end Erdos3

end

end OAI
