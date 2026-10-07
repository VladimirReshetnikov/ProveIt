import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteConvolution (f g : H → ℂ) (x : H) : ℂ :=
  𝔼 y, f y * g (x - y)

theorem finiteConvolution_fourier (f g : H → ℂ) (x : H) :
    finiteConvolution f g x =
      ∑ χ : AddChar H ℂ, (finiteFourierCoeff f χ * finiteFourierCoeff g χ) * χ x := by
  symm
  have hχ (χ : AddChar H ℂ) :
      (finiteFourierCoeff f χ * finiteFourierCoeff g χ) * χ x =
        𝔼 y, f y * (finiteFourierCoeff g χ * χ (x - y)) := by
    rw [mul_assoc, finiteFourierCoeff, Finset.expect_mul]
    apply Finset.expect_congr rfl
    intro y _
    rw [addChar_sub_star]
    ring
  simp_rw [hχ]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro y _
  rw [← Finset.mul_sum, finiteFourier_inversion]

theorem finiteConvolution_fourier_mass_sq (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ * finiteFourierCoeff g χ‖) ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  simp only [norm_mul]
  rw [← finiteFourier_parseval, ← finiteFourier_parseval]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

end Erdos3

end

end OAI
