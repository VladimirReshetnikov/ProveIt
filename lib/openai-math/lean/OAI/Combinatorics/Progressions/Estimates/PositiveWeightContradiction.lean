import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem weighted_comparison_of_uniform_approx {X : Type*} [Fintype X] [Nonempty X]
    (W H : X → ℂ) (F : X → ℝ) {eta B error : ℝ} (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x) (hmean : (𝔼 x, F x) ≤ B)
    (happrox : ∀ x, ‖W x - H x‖ ≤ eta)
    (hH : ‖(𝔼 x, H x * (F x : ℂ)) - (𝔼 x, H x)‖ ≤ error) :
    ‖(𝔼 x, W x * (F x : ℂ)) - (𝔼 x, W x)‖ ≤ error + eta * (B + 1) := by
  have herror : ‖𝔼 x, (W x - H x) * ((F x : ℂ) - 1)‖ ≤ eta * (B + 1) := by
    calc
      _ ≤ 𝔼 x, ‖(W x - H x) * ((F x : ℂ) - 1)‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 x, eta * (F x + 1) := by
        apply Finset.expect_le_expect
        intro x _
        have habs : |F x - 1| ≤ F x + 1 := abs_le.mpr ⟨by linarith [hF x], by linarith⟩
        have he : (F x : ℂ) - 1 = ((F x - 1 : ℝ) : ℂ) := by simp
        rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (happrox x) habs (abs_nonneg _) heta
      _ = eta * ((𝔼 x, F x) + 1) := by
        rw [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const]
      _ ≤ eta * (B + 1) := mul_le_mul_of_nonneg_left (add_le_add hmean le_rfl) heta
  have heq : (𝔼 x, W x * (F x : ℂ)) - (𝔼 x, W x) =
      ((𝔼 x, H x * (F x : ℂ)) - (𝔼 x, H x)) +
        (𝔼 x, (W x - H x) * ((F x : ℂ) - 1)) := by
    calc
      _ = 𝔼 x, (W x * (F x : ℂ) - W x) := (Finset.expect_sub_distrib ..).symm
      _ = 𝔼 x, ((H x * (F x : ℂ) - H x) + (W x - H x) * ((F x : ℂ) - 1)) := by
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_sub_distrib]
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hH herror)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positive_weight_counting_contradiction {X : Type*} [Fintype X] [Nonempty X]
    (W F : X → ℝ) (H : X → ℂ) {beta eta B error : ℝ}
    (hbeta : 0 < beta) (hW : beta ≤ 𝔼 x, W x) (hF : ∀ x, 0 ≤ F x)
    (hmean : (𝔼 x, F x) ≤ B) (hvanish : ∀ x, W x * F x = 0)
    (heta : 0 ≤ eta) (happrox : ∀ x, ‖(W x : ℂ) - H x‖ ≤ eta)
    (hcount : ‖(𝔼 x, H x * (F x : ℂ)) - (𝔼 x, H x)‖ ≤ error)
    (hsmall : error + eta * (B + 1) < beta) : False := by
  have h := weighted_comparison_of_uniform_approx (fun x => (W x : ℂ)) H F
    heta hF hmean happrox hcount
  have hv (x : X) : (W x : ℂ) * (F x : ℂ) = 0 := by
    rw [← Complex.ofReal_mul, hvanish, Complex.ofReal_zero]
  simp only [hv, Fintype.expect_const, zero_sub, norm_neg, ← complex_ofReal_expect,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbeta.le.trans hW)] at h
  linarith

end Erdos3

end

end OAI
