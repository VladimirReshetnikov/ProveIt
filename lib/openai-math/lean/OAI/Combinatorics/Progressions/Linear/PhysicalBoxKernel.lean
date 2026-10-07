import OAI.Combinatorics.Progressions.Sampling.SmoothPairPhysicalGrid

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem physicalBox_pair_kernel_grid_error {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ ρ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (b : Option J × I → ℤ)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1)
    (hlength : ∀ i c, ((P i).length c : ℝ) ≤ ρ * H i)
    (x y : translatedIntegerBox lo N) :
    |shiftedPairLocationKernel t u k hne H L hH hL b x.val y.val -
      shiftedPairLocationKernel t u k hne H L hH hL b
        (fun i => intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i))
        (fun i => intervalCellLower (lo i) (P i) (physicalBoxCell lo N P y i))| ≤
      (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ := by
  exact shiftedPairLocationKernel_grid_error t u k hne H L hH hL hC hκ hρ ht hu hgap b _ _ _ _
    (fun i => (physicalBoxCell_distance_lower lo N P hstep x i).trans (hlength i _))
    (fun i => (physicalBoxCell_distance_lower lo N P hstep y i).trans (hlength i _))

end Erdos3

end

end OAI
