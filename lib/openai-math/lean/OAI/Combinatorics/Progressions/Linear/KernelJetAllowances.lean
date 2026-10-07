import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def kernelJetInterpolationAllowance (q h : ℕ) (κ : ℝ) : ℝ :=
  (1 + (q : ℝ) * (2 * (q.factorial / κ))) ^ h

def kernelJetEntryAllowance (q h : ℕ) : ℝ := 2 ^ q * ((q : ℝ) + 1) ^ h

noncomputable def kernelJetMinorThreshold (q n j h : ℕ) (κ : ℝ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ h * kernelJetInterpolationAllowance q h κ) ^ j

noncomputable def kernelJetInverseAllowance (q n j h : ℕ) (κ : ℝ) : ℝ :=
  (j : ℝ) * ((j.factorial * (kernelJetEntryAllowance q h) ^ (j - 1)) /
    kernelJetMinorThreshold q n j h κ)

theorem kernelJetInterpolationAllowance_pos (q h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetInterpolationAllowance q h κ := by
  unfold kernelJetInterpolationAllowance
  positivity

theorem kernelJetEntryAllowance_pos (q h : ℕ) : 0 < kernelJetEntryAllowance q h := by
  unfold kernelJetEntryAllowance
  positivity

theorem kernelJetMinorThreshold_pos (q n j h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetMinorThreshold q n j h κ := by
  have := kernelJetInterpolationAllowance_pos q h hκ
  unfold kernelJetMinorThreshold
  positivity

theorem kernelJetInverseAllowance_nonneg (q n j h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ kernelJetInverseAllowance q n j h κ := by
  have := kernelJetEntryAllowance_pos q h
  have := kernelJetMinorThreshold_pos q n j h hκ
  unfold kernelJetInverseAllowance
  positivity

end Erdos3

end

end OAI
