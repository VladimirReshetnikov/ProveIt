import OAI.Combinatorics.Progressions.Geometry.GeometricSpectralBudgets

namespace OAI

section

namespace Erdos3

theorem initial_conditioning_prefactor_le_exp {sourceRatio siteRatio V W : ℝ} (n : ℕ)
    (hs0 : 0 ≤ sourceRatio) (ht0 : 0 ≤ siteRatio)
    (hs : sourceRatio ≤ Real.exp ((n : ℝ) * V))
    (ht : siteRatio ≤ Real.exp ((n : ℝ) * W)) :
    9 * sourceRatio * siteRatio * (2 : ℝ) ^ n ≤ Real.exp ((n : ℝ) * (V + W + 1) + 4) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hn : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) htwo n
      _ = _ := by rw [← Real.exp_nat_mul]; simp
  have h9 : (9 : ℝ) ≤ Real.exp 4 := by
    calc
      9 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp 4 * Real.exp ((n : ℝ) * V) * Real.exp ((n : ℝ) * W) * Real.exp (n : ℝ) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem initial_conditioning_error_small {sourceRatio siteRatio V W κ shell : ℝ} (n B : ℕ)
    (hs0 : 0 ≤ sourceRatio) (ht0 : 0 ≤ siteRatio)
    (hs : sourceRatio ≤ Real.exp ((n : ℝ) * V))
    (ht : siteRatio ≤ Real.exp ((n : ℝ) * W))
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hshell : 0 < shell)
    (hB : n + CyclicCrootSisask.spectralIterations shell ((n : ℝ) * (V + W + 1) + 4) ≤ B) :
    (2 : ℝ) ^ n * (κ ^ (B - n) * (sourceRatio * 3) * (siteRatio * 3)) ≤ shell / 16 := by
  have h := geometric_tail_after_cutoff hshell hκ0 hκhalf
    (by positivity : 0 ≤ 9 * sourceRatio * siteRatio * (2 : ℝ) ^ n)
    (initial_conditioning_prefactor_le_exp n hs0 ht0 hs ht)
    (show CyclicCrootSisask.spectralIterations shell ((n : ℝ) * (V + W + 1) + 4) ≤ B - n by omega)
  calc
    _ = κ ^ (B - n) * (9 * sourceRatio * siteRatio * (2 : ℝ) ^ n) := by ring
    _ ≤ shell / 16 := h

end Erdos3

end

end OAI
