import OAI.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteLayerBiasBudget (m : ℕ) (ζ : ℝ) : ℝ :=
  1 + ∑ i : Fin m, multiaffineBiasBudget i.val ζ

theorem finiteLayerBiasBudget_one_le (m : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    1 ≤ finiteLayerBiasBudget m ζ := by
  unfold finiteLayerBiasBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (multiaffineBiasBudget_pos i.val hζ).le))

theorem multiaffineBiasBudget_le_finite {m : ℕ} (i : Fin m) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget i.val ζ ≤ finiteLayerBiasBudget m ζ := by
  apply le_trans (Finset.single_le_sum (fun j _ => (multiaffineBiasBudget_pos j.val hζ).le)
    (Finset.mem_univ i))
  exact le_add_of_nonneg_left zero_le_one

noncomputable def layerRemovalRankBudget (m d : ℕ) (C D B A S : ℝ) : ℝ :=
  1 + ∑ i : Fin m,
    (((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) +
      (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) +
      (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B))

theorem layerRemovalRankBudget_bounds {m : ℕ} (i : Fin m) (d : ℕ)
    {C D B A S : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (hA : 0 ≤ A) (hS : 0 ≤ S) :
    ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) ≤ layerRemovalRankBudget m d C D B A S ∧
    (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) ≤ layerRemovalRankBudget m d C D B A S ∧
    (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) ≤ layerRemovalRankBudget m d C D B A S := by
  let cost (j : Fin m) :=
    ((j.val + 1).factorial : ℝ) * (C * D ^ (j.val + 1)) +
      (B * S ^ (j.val + 1)) ^ (d ^ (j.val + 1)) +
      (d : ℝ) ^ (j.val + 1) * (A ^ (j.val + 1) * B)
  have hcost j : 0 ≤ cost j := by dsimp [cost]; positivity
  have hs : cost i ≤ ∑ j : Fin m, cost j :=
    Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  have ht : cost i ≤ layerRemovalRankBudget m d C D B A S := by
    exact hs.trans (le_add_of_nonneg_left zero_le_one)
  have hrow : 0 ≤ ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) := by positivity
  have hden : 0 ≤ (B * S ^ (i.val + 1)) ^ (d ^ (i.val + 1)) := by positivity
  have hcoeff : 0 ≤ (d : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) := by positivity
  dsimp [cost] at ht
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
