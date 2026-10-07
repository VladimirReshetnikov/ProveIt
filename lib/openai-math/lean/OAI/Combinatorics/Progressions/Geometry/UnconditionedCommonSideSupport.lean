import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem unconditionedResidueSiteBound_le_commonSide
    {K J : Type*} [Fintype K] [Fintype J]
    (P : J → ℕ) (e : K ≃ J) (S : ℕ) (hP : ∀ j, P j ≤ S) :
    unconditionedResidueSiteBound P ≤ (Fintype.card K : ℝ) * S := by
  calc
    unconditionedResidueSiteBound P ≤ ∑ _j : J, (S : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast hP j
    _ = (Fintype.card K : ℝ) * S := by
      simp [Fintype.card_congr e]

theorem integerBox_commonSide_sum_abs_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ) (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
    (∑ k, |(x k : ℝ)|) ≤ (Fintype.card K : ℝ) * S := by
  calc
    (∑ k, |(x k : ℝ)|) ≤ ∑ _k : K, (S : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hk := (mem_integerBox (fun _ : K => S) x).mp hx k
      rw [abs_of_nonneg (by exact_mod_cast hk.1 : (0 : ℝ) ≤ x k)]
      exact_mod_cast hk.2.le
    _ = (Fintype.card K : ℝ) * S := by simp

namespace BooleanCubeKernel

theorem unconditionedCommonSide_site_mem
    {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (S : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (N : X → ℕ)
    (hR : ∀ i, 2 * spatialTrimMargin τ N i < N i)
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N) 1)
    (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
    jointIntegerPhysicalSite x (z.1.val, z.2.val) ∈ integerBox N := by
  apply jointIntegerPhysicalSite_mem_box x N (spatialTrimMargin τ N)
    (fun i => (hR i).le)
    (trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N) _ z
  intro i
  exact spatialTrimMargin_fits (by positivity) hτ x
    (integerBox_commonSide_sum_abs_le S x hx) N i

end BooleanCubeKernel
end Erdos3

end

end OAI
