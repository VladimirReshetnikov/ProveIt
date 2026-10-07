import OAI.Combinatorics.Progressions.Dynamics.SpectralLogBudget
import OAI.Combinatorics.Progressions.Fourier.LocalSpectrumBudget

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def samplingCubicFactor (epsilon : ℝ) : ℝ :=
  2 * (256 * Real.exp 1 ^ 2 / (epsilon / 8) ^ 2) * spectralIterationFactor epsilon ^ 2 + 1

theorem samplingCubicFactor_pos (epsilon : ℝ) : 0 < samplingCubicFactor epsilon := by
  unfold samplingCubicFactor
  positivity

theorem local_sample_size_le_cubic {N : ℕ} (M L : Finset (ZMod N))
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp (2 * p)) :
    (crootSisaskSampleSize (convolutionMomentOrder M L)
      (((epsilon / 8) / spectralIterations epsilon p) / Real.exp 1) : ℝ) ≤
        samplingCubicFactor epsilon * (p + 1) ^ 3 := by
  let q := spectralIterations epsilon p
  let H := 256 * Real.exp 1 ^ 2 / (epsilon / 8) ^ 2
  have hH : 0 ≤ H := by positivity
  have hq := spectralIterations_le hepsilon hepsilon1 hp
  have hraw := localBoostedSampleSize_le M L (p := 2 * p) (by positivity) hratio
    (by positivity : 0 < epsilon / 8) q (spectralIterations_pos epsilon p)
  have hp1 : 1 ≤ p + 1 := by linarith
  have hp3 : 1 ≤ (p + 1) ^ 3 := one_le_pow₀ hp1
  calc
    _ ≤ H * (2 * p + 2) * (q : ℝ) ^ 2 + 1 := hraw
    _ ≤ H * (2 * p + 2) * (spectralIterationFactor epsilon * (p + 1)) ^ 2 + 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg q) hq 2) (mul_nonneg hH (by positivity))) le_rfl
    _ = (2 * H * spectralIterationFactor epsilon ^ 2) * (p + 1) ^ 3 + 1 := by ring
    _ ≤ samplingCubicFactor epsilon * (p + 1) ^ 3 := by
      unfold samplingCubicFactor
      dsimp [H]
      nlinarith

noncomputable def rankQuarticFactor (epsilon : ℝ) : ℝ :=
  8 * (1 + Real.log 4 + samplingCubicFactor epsilon)

theorem rankQuarticFactor_pos (epsilon : ℝ) : 0 < rankQuarticFactor epsilon := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC := samplingCubicFactor_pos epsilon
  unfold rankQuarticFactor
  positivity

end Erdos3.CyclicCrootSisask

namespace Erdos3.RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem local_dimension_le_quartic_of_cubic_sampling
    (B : CyclicBohr.Set N) {T : Finset (ZMod N)} (hT : T.Nonempty)
    {p C : ℝ} (hp : 0 ≤ p) (_hC : 0 ≤ C) (k : ℕ)
    (hk : (k : ℝ) ≤ C * (p + 1) ^ 3)
    (hcount : (B.carrier.card : ℝ) / (2 * (2 * Real.exp p) ^ k) ≤ T.card) :
    localChangDimension B T (1 / 2) ≤ 8 * (1 + Real.log 4 + C) * (p + 1) ^ 4 := by
  have hdim := localChangDimension_half_le_of_card B hT
    (by positivity : 0 < 2 * Real.exp p) k hcount
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogK : Real.log (2 * Real.exp p) ≤ p + 1 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero p), Real.log_exp]
    linarith
  have hprod : (k : ℝ) * Real.log (2 * Real.exp p) ≤ C * (p + 1) ^ 4 := by
    calc
      _ ≤ (k : ℝ) * (p + 1) := mul_le_mul_of_nonneg_left hlogK (Nat.cast_nonneg _)
      _ ≤ (C * (p + 1) ^ 3) * (p + 1) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = C * (p + 1) ^ 4 := by ring
  have hp4 : 1 ≤ (p + 1) ^ 4 := one_le_pow₀ (show 1 ≤ p + 1 by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hconst : 1 + Real.log 4 ≤ (1 + Real.log 4) * (p + 1) ^ 4 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp4 (by positivity : 0 ≤ 1 + Real.log 4)
  nlinarith

end Erdos3.RelativeChangSanders

end

end OAI
