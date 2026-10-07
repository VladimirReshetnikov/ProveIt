import OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct
import OAI.Combinatorics.Progressions.Estimates.FiniteConvolution

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersNorm_mul_fourier (j : ℕ) (f : H → ℂ) (a : AddChar H ℂ → ℂ) :
    gowersNorm (j + 2) (fun x => f x * (∑ χ : AddChar H ℂ, a χ * χ x)) ≤
      (∑ χ : AddChar H ℂ, ‖a χ‖) * gowersNorm (j + 2) f := by
  simp only [Finset.mul_sum]
  apply (gowersNorm_sum (j + 1) _).trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  have he : (fun x => f x * (a χ * χ x)) = (fun x => a χ * (χ x * f x)) := by
    funext x
    ring
  rw [he, gowersNorm_const_mul, gowersNorm_mul_character j χ f χ.map_add_eq_mul χ.norm_apply]

theorem gowersNorm_mul_convolution (j : ℕ) (f u v : H → ℂ) :
    gowersNorm (j + 2) (fun x => f x * finiteConvolution u v x) ≤
      (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff u χ * finiteFourierCoeff v χ‖) *
        gowersNorm (j + 2) f := by
  simp only [finiteConvolution_fourier]
  exact gowersNorm_mul_fourier j f _

theorem gowersNorm_mul_approximation (j : ℕ) (f u v : H → ℂ) {M ε : ℝ}
    (hε : 0 ≤ ε) (hf : ∀ x, ‖f x‖ ≤ 1) (huv : ∀ x, ‖u x - v x‖ ≤ 1)
    (herror : (𝔼 x, ‖u x - v x‖) ≤ ε ^ (2 ^ (j + 2)))
    (hmult : gowersNorm (j + 2) (fun x => f x * v x) ≤ M * gowersNorm (j + 2) f) :
    gowersNorm (j + 2) (fun x => f x * u x) ≤ M * gowersNorm (j + 2) f + ε := by
  let e := fun x => f x * (u x - v x)
  have heunit (x : H) : ‖e x‖ ≤ 1 := by
    simpa only [e, norm_mul, one_mul] using mul_le_mul (hf x) (huv x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hepoint (x : H) : ‖e x‖ ≤ ‖u x - v x‖ := by
    simpa only [e, norm_mul, one_mul] using mul_le_mul_of_nonneg_right (hf x) (norm_nonneg (u x - v x))
  have he : gowersNorm (j + 2) e ≤ ε :=
    gowersNorm_le_of_mean_norm_le_pow (j + 1) e heunit hε
      ((Finset.expect_le_expect (fun x _ => hepoint x)).trans herror)
  have hsplit : (fun x => f x * u x) = (fun x => f x * v x + e x) := by
    funext x
    dsimp [e]
    ring
  rw [hsplit]
  exact (gowersNorm_add (j + 1) _ _).trans (add_le_add hmult he)

end Erdos3

end

end OAI
