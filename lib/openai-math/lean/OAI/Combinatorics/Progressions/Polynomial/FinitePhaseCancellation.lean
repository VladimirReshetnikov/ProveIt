import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem circle_character_mul_star (θ : CircleFourier.Circle) :
    character θ * star (character θ) = 1 := by
  rw [← character_neg, ← character_add, add_neg_cancel, character_zero]

theorem finite_phase_cancellation {I : Type*} [Fintype I]
    (v : ℂ) (w : I → ℂ) (θ₀ : CircleFourier.Circle) (θ : I → CircleFourier.Circle)
    (hθ : θ₀ = ∑ i, θ i) :
    (character θ₀ * v) * star (∏ i, character (θ i) * w i) = v * star (∏ i, w i) := by
  rw [Finset.prod_mul_distrib, ← character_fintype_sum, ← hθ, star_mul]
  calc
    _ = (character θ₀ * star (character θ₀)) * (v * star (∏ i, w i)) := by ring
    _ = _ := by rw [circle_character_mul_star, one_mul]

theorem power_phase_cancellation (n : ℕ) (v : ℂ) (w : Fin n → ℂ)
    (θ : CircleFourier.Circle) :
    (character (n • θ) * v) * star (∏ i, character θ * w i) = v * star (∏ i, w i) := by
  exact finite_phase_cancellation v w (n • θ) (fun _ => θ) (by simp)

end Erdos3

end

end OAI
