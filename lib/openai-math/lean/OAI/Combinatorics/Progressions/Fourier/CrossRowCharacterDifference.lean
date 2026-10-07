import OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct
import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def characterCrossRow (f g : G → ℂ) (χ : G → AddChar G ℂ) (h n : G) : ℂ :=
  (f n * star (g (n + h))) * star (χ h n)

theorem characterCrossRow_norm (f g : G → ℂ) (χ : G → AddChar G ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (h n : G) :
    ‖characterCrossRow f g χ h n‖ ≤ 1 := by
  simp only [characterCrossRow, norm_mul, norm_star, AddChar.norm_apply, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))

theorem characterCrossRow_derivative (f g : G → ℂ) (χ : G → AddChar G ℂ) (h k n : G) :
    multiplicativeDerivative (characterCrossRow f g χ h) k n =
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) * χ h k := by
  have hcancel : χ h n * star (χ h n) = 1 := by
    change χ h n * (starRingEnd ℂ) (χ h n) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    norm_num
  have hshift : n + k + h = n + h + k := by abel
  simp only [characterCrossRow, multiplicativeDerivative, star_mul, star_star,
    (χ h).map_add_eq_mul, hshift]
  calc
    _ = (((f n * star (f (n + k))) * (star (g (n + h)) * g (n + h + k))) * χ h k) *
        (χ h n * star (χ h n)) := by ring
    _ = _ := by rw [hcancel, mul_one]; ring

theorem characterCrossRow_derivative_correlation_norm (f g : G → ℂ)
    (χ : G → AddChar G ℂ) (h k : G) (K : G → ℂ) :
    ‖𝔼 n, multiplicativeDerivative (characterCrossRow f g χ h) k n * star (K n)‖ =
      ‖𝔼 n, (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K n)‖ := by
  have heq : (𝔼 n, multiplicativeDerivative (characterCrossRow f g χ h) k n * star (K n)) =
      χ h k * (𝔼 n, (multiplicativeDerivative f k n *
        star (multiplicativeDerivative g k (n + h))) * star (K n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [characterCrossRow_derivative]
    ring
  rw [heq, norm_mul, AddChar.norm_apply, one_mul]

end Erdos3

end

end OAI
