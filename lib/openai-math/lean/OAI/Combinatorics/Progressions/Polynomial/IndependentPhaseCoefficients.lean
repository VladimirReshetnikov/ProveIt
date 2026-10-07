/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem independent_phase_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {Ω : B → Type*} [∀ b, Fintype (Ω b)] (p : ∀ b, FiniteProbabilityWeights (Ω b))
    (F : ∀ b, Ω b → CircleFourier.Circle) (shift : CircleFourier.Circle) :
    (FiniteProbabilityWeights.pi p).complexMean (fun x => character (shift + ∑ b, F b (x b))) =
      character shift * ∏ b, (p b).complexMean (fun x => character (F b x)) := by
  simp only [character_add, character_fintype_sum]
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  congr 1
  exact FiniteProbabilityWeights.complexMean_pi_product p (fun b x => character (F b x))

theorem norm_independent_phase_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {Ω : B → Type*} [∀ b, Fintype (Ω b)] (p : ∀ b, FiniteProbabilityWeights (Ω b))
    (F : ∀ b, Ω b → CircleFourier.Circle) (shift : CircleFourier.Circle) :
    ‖(FiniteProbabilityWeights.pi p).complexMean (fun x => character (shift + ∑ b, F b (x b)))‖ =
      ∏ b, ‖(p b).complexMean (fun x => character (F b x))‖ := by
  rw [independent_phase_coefficient, norm_mul, norm_character, one_mul, norm_prod]

theorem norm_product_coefficients_le {B : Type*} [Fintype B] (c : B → ℂ) {ζ : ℝ}
    (h : ∀ b, ‖c b‖ ≤ ζ) : ‖∏ b, c b‖ ≤ ζ ^ Fintype.card B := by
  classical
  rw [norm_prod]
  calc
    _ ≤ ∏ _b : B, ζ :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun index _ => h index)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
