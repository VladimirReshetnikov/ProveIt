import OAI.Combinatorics.Progressions.Fourier.ElementaryCharacterTail
import OAI.Combinatorics.Progressions.Probability.LargeCokernelProbability

namespace OAI

section

namespace Erdos3

theorem largeCokernel_reciprocal_probability_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (B R : ℕ) (hB : 0 < B) (C : ℝ) (hC : 0 ≤ C)
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2))
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤
        C / (a : ℝ) ^ (1 / (Fintype.card I : ℝ))) :
    (FiniteProbabilityWeights.pi p).eventProbability (largeCokernelEvent column B R) ≤
      C ^ Fintype.card J / (B : ℝ) := by
  have h := largeCokernel_probability_le p column B R
    (fun a => C / (a : ℝ) ^ (1 / (Fintype.card I : ℝ)))
    (fun a => div_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg a) _)) hsingle
  rw [hJ] at h ⊢
  exact h.trans (finite_character_reciprocal_tail B R (Fintype.card I) hB
    Fintype.card_pos C hC)

end Erdos3

end

end OAI
