import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz

namespace OAI

section

namespace Erdos3

noncomputable def relativeScalarPassageSlack (τ : ℝ) : ℝ := τ / (2 * (1 - τ))

theorem relativeScalarPassageSlack_bounds {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    0 < relativeScalarPassageSlack τ ∧ relativeScalarPassageSlack τ ≤ 1 := by
  have hd : 0 < 2 * (1 - τ) := by linarith
  exact ⟨div_pos hτ hd, (div_le_one hd).mpr (by linarith)⟩

theorem relativeScalarPassageSlack_level {τ Λ : ℝ} (hτ : τ < 1) :
    (1 + relativeScalarPassageSlack τ) * ((1 - τ) * Λ) = (1 - τ / 2) * Λ := by
  unfold relativeScalarPassageSlack
  have hd : 1 - τ ≠ 0 := by linarith
  field_simp
  ring

theorem relativeScalarPassageScore_le {τ Λ f g : ℝ}
    (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hΛ : 0 ≤ Λ) (hg : 0 ≤ g) :
    (f - Λ) * g ≤ f * g -
      (1 + relativeScalarPassageSlack τ) * ((1 - τ) * Λ) * g := by
  rw [relativeScalarPassageSlack_level (by linarith : τ < 1)]
  nlinarith [mul_nonneg (mul_nonneg hτ.le hΛ) hg]

theorem relativeScalarPassage_mesh_score
    {Ω : Type*} [Fintype Ω] (original mesh : FiniteProbabilityWeights Ω)
    (f g : Ω → ℝ) {τ Λ δ η : ℝ}
    (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hΛ : 0 ≤ Λ) (hg : ∀ x, 0 ≤ g x)
    (hscore : δ ≤ original.mean (fun x => (f x - Λ) * g x))
    (happrox : |original.mean (fun x => (f x - Λ) * g x) -
      mesh.mean (fun x => (f x - Λ) * g x)| ≤ η) :
    δ - η ≤ mesh.mean (fun x => f x * g x -
      (1 + relativeScalarPassageSlack τ) * ((1 - τ) * Λ) * g x) := by
  have hnear := (abs_le.mp happrox).2
  calc
    δ - η ≤ mesh.mean (fun x => (f x - Λ) * g x) := by linarith
    _ ≤ _ := mesh.mean_mono (fun x => relativeScalarPassageScore_le hτ hτhalf hΛ (hg x))

end Erdos3

end

end OAI
