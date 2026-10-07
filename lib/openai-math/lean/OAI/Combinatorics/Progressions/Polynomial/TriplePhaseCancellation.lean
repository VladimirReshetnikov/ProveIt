import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

namespace Erdos3

theorem circle_character_triple_cancel (a b : CircleFourier.Circle) :
    CircleFourier.character (a + b) * star (CircleFourier.character a) *
      star (CircleFourier.character b) = 1 := by
  rw [← CircleFourier.character_neg, ← CircleFourier.character_neg,
    ← CircleFourier.character_add, ← CircleFourier.character_add]
  convert CircleFourier.character_zero using 1
  congr 1
  abel

theorem triple_phase_cancellation (v : Fin 3 → ℂ) (θ : Fin 3 → CircleFourier.Circle)
    (hθ : θ 0 = θ 1 + θ 2) :
    (CircleFourier.character (θ 0) * v 0) * star (CircleFourier.character (θ 1) * v 1) *
      star (CircleFourier.character (θ 2) * v 2) = v 0 * star (v 1) * star (v 2) := by
  rw [star_mul, star_mul]
  calc
    _ = (CircleFourier.character (θ 0) * star (CircleFourier.character (θ 1)) *
        star (CircleFourier.character (θ 2))) * (v 0 * star (v 1) * star (v 2)) := by ring
    _ = _ := by rw [hθ, circle_character_triple_cancel, one_mul]

end Erdos3

end

end OAI
