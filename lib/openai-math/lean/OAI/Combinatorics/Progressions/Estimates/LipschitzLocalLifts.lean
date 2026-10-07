import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y E : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [NormedAddCommGroup E]

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
theorem reconstruction_norm_le (π : X → Y) (hπ : Function.Surjective π)
    (f : X → E) (F : Y → E) (hF : ∀ x, F (π x) = f x) {B : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ B) : ∀ y, ‖F y‖ ≤ B := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  rw [hF]
  exact hbound x

theorem lipschitz_reconstruction_of_local_lifts (π : X → Y) (hπ : Function.Surjective π)
    (f : X → E) (F : Y → E) (hF : ∀ x, F (π x) = f x)
    (L K B δ : ℝ≥0) (hδ : 0 < δ) (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlift : ∀ y z : Y, dist y z < δ →
      ∃ x x' : X, π x = y ∧ π x' = z ∧ dist x x' ≤ K * dist y z) :
    LipschitzWith (max (L * K) (2 * B / δ)) F := by
  have hFbound := reconstruction_norm_le π hπ f F hF hbound
  have hδr : (0 : ℝ) < δ := hδ
  apply LipschitzWith.of_dist_le_mul
  intro y z
  by_cases hyz : dist y z < δ
  · obtain ⟨x, x', hx, hx', hdist⟩ := hlift y z hyz
    rw [← hx, ← hx', hF, hF]
    calc
      dist (f x) (f x') ≤ L * dist x x' := hf.dist_le_mul x x'
      _ ≤ (L : ℝ) * (K * dist (π x) (π x')) := by
        rw [hx, hx']
        exact mul_le_mul_of_nonneg_left hdist L.coe_nonneg
      _ = ((L * K : ℝ≥0) : ℝ) * dist (π x) (π x') := by simp only [NNReal.coe_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left (L * K) (2 * B / δ)) dist_nonneg
  · have hdist : (δ : ℝ) ≤ dist y z := le_of_not_gt hyz
    calc
      dist (F y) (F z) ≤ ‖F y‖ + ‖F z‖ := dist_le_norm_add_norm _ _
      _ ≤ (2 : ℝ) * B := by linarith [hFbound y, hFbound z]
      _ = (2 * (B : ℝ) / δ) * δ := (div_mul_cancel₀ _ hδr.ne').symm
      _ ≤ (2 * (B : ℝ) / δ) * dist y z := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = ((2 * B / δ : ℝ≥0) : ℝ) * dist y z := by simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right (L * K) (2 * B / δ)) dist_nonneg

end Erdos3

end

end OAI
