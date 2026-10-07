import OAI.Combinatorics.Progressions.Estimates.ShiftTestingGowers

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_square_family_eq_cross_re {H Ω : Type*} [Fintype H] [Fintype Ω]
    (v : H → Ω → ℂ) :
    (𝔼 x, ‖𝔼 h, v h x‖ ^ 2) = (𝔼 h, 𝔼 k, 𝔼 x, v h x * star (v k x)).re := by
  simp_rw [square_norm_mean_eq_cross_re]
  rw [← expect_re, Finset.expect_comm]
  congr 1
  apply Finset.expect_congr rfl
  intro h _
  exact Finset.expect_comm _ _ _

theorem finite_family_cauchy_schwarz_re {H Ω : Type*} [Fintype H] [Fintype Ω]
    [Nonempty Ω] (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    ‖𝔼 x, B x * (𝔼 h, v h x)‖ ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, 𝔼 x, v h x * star (v k x)).re := by
  have hcs := norm_expect_mul_star_sq_le B (fun x => star (𝔼 h, v h x))
  simp only [star_star, norm_star] at hcs
  have hBM : (𝔼 x, ‖B x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)).trans_eq (Fintype.expect_const _)
  rw [← mean_square_family_eq_cross_re]
  exact hcs.trans (mul_le_mul_of_nonneg_right hBM
    (Finset.expect_nonneg (fun x _ => sq_nonneg _)))

theorem norm_expect_sq_le_expect_norm_sq {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (v : Ω → ℂ) : ‖𝔼 x, v x‖ ^ 2 ≤ 𝔼 x, ‖v x‖ ^ 2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (RCLike.norm_expect_le (K := ℂ)) 2).trans
    (expect_square_le (fun x => ‖v x‖))

end Erdos3

end

end OAI
