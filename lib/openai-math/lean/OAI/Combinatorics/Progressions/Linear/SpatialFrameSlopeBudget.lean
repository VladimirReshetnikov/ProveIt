import OAI.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap

namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]

theorem narrowSpatial_frame_slope_bound
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (v : Option (G ⊕ J) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (k : G ⊕ J) (x : X) :
    |(v (some k, x) : ℝ)| ≤ τ * (N x : ℝ) / (8 * (1 + W)) := by
  have h := (rectangularWeightIndices_zero_bound _ hv (some k, x)).trans
    (narrowTrimmedSpatialWidths_le hW hτ hξ N hN (some k, x))
  simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul, mul_div_assoc] using h

theorem narrowSpatial_frame_slope_sum
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (v : Option (G ⊕ J) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (x : X) :
    (∑ k, |(v (some k, x) : ℝ)| * T k) ≤ τ * (N x : ℝ) / 8 := by
  have hden : 0 < 8 * (1 + W) := by positivity
  have hcoef : 0 ≤ τ * (N x : ℝ) / (8 * (1 + W)) := by positivity
  calc
    _ ≤ ∑ k, (τ * (N x : ℝ) / (8 * (1 + W))) * T k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
        (narrowSpatial_frame_slope_bound hW hτ hξ N hN v hv k x) (hT k))
    _ = (τ * (N x : ℝ) / (8 * (1 + W))) * ∑ k, T k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (τ * (N x : ℝ) / (8 * (1 + W))) * (1 + W) :=
      mul_le_mul_of_nonneg_left (hsum.trans (by linarith)) hcoef
    _ = τ * (N x : ℝ) / 8 := by
      have hw : 1 + W ≠ 0 := by positivity
      field_simp

theorem narrowSpatial_frame_normalized_slope_sum
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (v : Option (G ⊕ J) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (x : X) :
    (∑ k, |(v (some k, x) : ℝ) / (N x : ℝ)| * T k) ≤ τ / 8 := by
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN x
  have h := narrowSpatial_frame_slope_sum hW hτ hξ N hN T hT hsum v hv x
  have hd : (∑ k, |(v (some k, x) : ℝ)| * T k) / (N x : ℝ) ≤ τ / 8 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  calc
    _ = (∑ k, |(v (some k, x) : ℝ)| * T k) / (N x : ℝ) := by
      simp only [abs_div, abs_of_pos hn, div_mul_eq_mul_div, Finset.sum_div]
    _ ≤ τ / 8 := hd

end Erdos3

end

end OAI
