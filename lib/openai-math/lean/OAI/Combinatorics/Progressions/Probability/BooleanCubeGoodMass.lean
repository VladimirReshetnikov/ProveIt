import OAI.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem booleanCubeGoodWeight_mass_error {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (κ : J → ℝ) (hκ : ∀ i, 0 < κ i) {η : ℝ} (hη : 0 < η)
    (hprob : (∑ j, (blockCubeMeasure B (Fin h) α).real
      {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) a| < 2 * κ j}) ≤ η / 2) :
    1 - η ≤ ∫ a, booleanCubeGoodWeight c sets block v sel ψ
      (fun _ => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2)) κ a := by
  have hhalf : 0 < η / 2 := half_pos hη
  have hr := scalarCubeProductBoundaryRadius_pos (B × Fin h) α hhalf
  have hweight := booleanCubeGoodWeight_mass_lower c sets block v sel ψ hψ hrange hone
    (fun _ => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2)) (fun _ => hr) κ hκ
  have hb := scalarCubeProductBoundaryRadius_loss (B × Fin h) α hhalf
  linarith

end Erdos3

end

end OAI
