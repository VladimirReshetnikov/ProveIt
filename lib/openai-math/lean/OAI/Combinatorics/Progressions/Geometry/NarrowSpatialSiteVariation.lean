import OAI.Combinatorics.Progressions.Linear.SpatialFrameSlopeBudget

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem jointIntegerPhysicalSite_normalized_dist_of_slope_sum
    {K X : Type*} [Fintype K] [Fintype X]
    (N : X → ℕ) (T : K → ℝ) (a : X → ℤ) (frame : Option K × X → ℤ)
    (u v : K → ℤ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hslope : ∀ x, (∑ k, |(frame (some k, x) : ℝ) / N x| * T k) ≤ C)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ C * δ := by
  apply (dist_pi_le_iff (mul_nonneg hC hδ)).mpr
  intro x
  rw [Real.dist_eq]
  have hraw : (jointIntegerPhysicalSite u (a, frame) x : ℝ) -
      (jointIntegerPhysicalSite v (a, frame) x : ℝ) =
      ∑ k, ((u k : ℝ) - (v k : ℝ)) * (frame (some k, x) : ℝ) := by
    calc
      _ = (∑ k, (u k : ℝ) * (frame (some k, x) : ℝ)) -
          ∑ k, (v k : ℝ) * (frame (some k, x) : ℝ) := by
        simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
          Int.cast_add, Int.cast_sum, Int.cast_mul]
        ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have heq : (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x -
      (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x =
      ∑ k, ((u k : ℝ) - (v k : ℝ)) * ((frame (some k, x) : ℝ) / N x) := by
    rw [← sub_div, hraw, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  calc
    _ ≤ ∑ k, |((u k : ℝ) - (v k : ℝ)) * ((frame (some k, x) : ℝ) / N x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (T k * δ) * |(frame (some k, x) : ℝ) / N x| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcell k) (abs_nonneg _)
    _ = (∑ k, |(frame (some k, x) : ℝ) / N x| * T k) * δ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hslope x) hδ

theorem narrowSpatial_jointPhysicalSite_normalized_dist
    {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (a : X → ℤ) (frame : Option (G ⊕ J) × X → ℤ)
    (hframe : frame ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (u v : G ⊕ J → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ τ * δ / 8 := by
  have h := jointIntegerPhysicalSite_normalized_dist_of_slope_sum N T a frame u v
    (by positivity : 0 ≤ τ / 8) hδ
    (narrowSpatial_frame_normalized_slope_sum hW hτ hξ N hN T hT hsum frame hframe) hcell
  simpa only [div_mul_eq_mul_div] using h

theorem narrowSpatial_jointPhysicalSite_normalized_dist_le_cell
    {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (a : X → ℤ) (frame : Option (G ⊕ J) × X → ℤ)
    (hframe : frame ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (u v : G ⊕ J → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ δ := by
  apply (narrowSpatial_jointPhysicalSite_normalized_dist hW hτ hξ N hN T hT hsum
    a frame hframe u v hδ hcell).trans
  have h := mul_le_mul_of_nonneg_right hτ1 hδ
  nlinarith

end Erdos3

end

end OAI
