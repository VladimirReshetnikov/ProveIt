import OAI.Combinatorics.Progressions.Dynamics.SpectralLogBudget
import OAI.Combinatorics.Progressions.Estimates.EvenMomentChoice

namespace OAI

section

namespace Erdos3

noncomputable def affineRemovalDepth (T : ℝ) : ℕ := CyclicCrootSisask.spectralIterations 1 T

noncomputable def affineFinalDegree (j r : ℕ) (shell Q : ℝ) : ℕ :=
  j + max r (CyclicCrootSisask.spectralIterations shell Q)

theorem affineRemovalDepth_cutoff (T : ℝ) :
    2 ≤ Real.exp (-T) * (2 : ℝ) ^ (affineRemovalDepth T + 1) := by
  have h := CyclicCrootSisask.half_pow_spectralIterations_mul_exp_le (p := T) (by norm_num : (0 : ℝ) < 1)
  have hp : 0 < (2 : ℝ) ^ affineRemovalDepth T := by positivity
  have hm := mul_le_mul_of_nonneg_right h hp.le
  have he : ((1 / 2 : ℝ) ^ CyclicCrootSisask.spectralIterations 1 T * Real.exp T) *
      (2 : ℝ) ^ affineRemovalDepth T = Real.exp T := by
    unfold affineRemovalDepth
    rw [div_pow, one_pow]
    field_simp
  rw [he] at hm
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-T)).le
  have hc : Real.exp (-T) * Real.exp T = 1 := by rw [← Real.exp_add]; simp
  rw [hc] at hh
  rw [pow_succ]
  nlinarith

theorem affineRemovalDepth_le {T : ℝ} (hT : 0 ≤ T) :
    (affineRemovalDepth T : ℝ) ≤ CyclicCrootSisask.spectralIterationFactor 1 * (T + 1) :=
  CyclicCrootSisask.spectralIterations_le (by norm_num) le_rfl hT

theorem affineFinalDegree_bounds (j r : ℕ) (shell Q : ℝ) :
    j + r ≤ affineFinalDegree j r shell Q ∧
    j + CyclicCrootSisask.spectralIterations shell Q ≤ affineFinalDegree j r shell Q := by
  unfold affineFinalDegree
  omega

theorem affineFinalDegree_le (j r : ℕ) {shell Q : ℝ}
    (hshell : 0 < shell) (hshell1 : shell ≤ 1) (hQ : 0 ≤ Q) :
    (affineFinalDegree j r shell Q : ℝ) ≤ (j : ℝ) + r +
      CyclicCrootSisask.spectralIterationFactor shell * (Q + 1) := by
  have h := CyclicCrootSisask.spectralIterations_le hshell hshell1 hQ
  have hn : affineFinalDegree j r shell Q ≤ j + r + CyclicCrootSisask.spectralIterations shell Q := by
    unfold affineFinalDegree
    omega
  have hn' : (affineFinalDegree j r shell Q : ℝ) ≤ (j : ℝ) + r +
      (CyclicCrootSisask.spectralIterations shell Q : ℝ) := by exact_mod_cast hn
  linarith

end Erdos3

end

end OAI
