import OAI.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
import OAI.Combinatorics.Progressions.Probability.ScalarCubeWindowLaw

namespace OAI

section

namespace Erdos3

theorem exists_window_good_scalar_kernel_bound (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) :
    ∃ s : I ↪ J, ∀ (M D : ℕ), 0 < M → ∀ hD : 0 < D, ∀ η : ℝ, 0 < η → ∃ B L₀ : ℕ,
      0 < B ∧ ∃ hsize : D * ((Fintype.card I + 1) * M) ≤ L₀,
      ∀ (L : ℕ) (hL : 0 < L) (hlarge : L₀ ≤ L) (K : J → ℕ)
        (hKL : ∀ j, K j ≤ L) (hDK : ∀ j, L ≤ D * K j)
        (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
        (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M),
        (FiniteProbabilityWeights.pi (fun j =>
          scalarCubeWindowWeights I L (K j) M D hL (hKL j) (hDK j)
            (m j) (r j) (hm j) (hmM j)
            (scalarCubeWindow_size hD (hsize.trans hlarge) (hDK j)))).eventProbability
              (fun x => ¬ GoodScalarKernelTuple s (1 / (B : ℝ)) B x) ≤ η := by
  obtain ⟨s, hs⟩ := exists_uniform_good_scalar_kernel_bound I J hJ
  refine ⟨s, fun M D hM hD η hη => ?_⟩
  let C := (scalarCubeResidueDensityCap I (M * D)) ^ Fintype.card J
  have hC : 0 < C := pow_pos (scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD)) _
  obtain ⟨B, L₁, hB, hL₁, hprob⟩ := hs (η / C) (div_pos hη hC)
  refine ⟨B, max L₁ (D * ((Fintype.card I + 1) * M)), hB, Nat.le_max_right _ _, ?_⟩
  intro L hL hlarge K hKL hDK m r hm hmM
  have hsize : ∀ j, (Fintype.card I + 1) * M ≤ K j := fun j =>
    scalarCubeWindow_size hD ((Nat.le_max_right _ _).trans hlarge) (hDK j)
  calc
    _ ≤ C * (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (fun x => ¬ GoodScalarKernelTuple s (1 / (B : ℝ)) B x) :=
      scalarCubeWindow_pi_eventProbability_le I J L M D K hL hKL hDK m r hm hmM hsize _
    _ ≤ C * (η / C) := mul_le_mul_of_nonneg_left
      (hprob L hL ((Nat.le_max_left _ _).trans hlarge)) hC.le
    _ = η := by field_simp

end Erdos3

end

end OAI
