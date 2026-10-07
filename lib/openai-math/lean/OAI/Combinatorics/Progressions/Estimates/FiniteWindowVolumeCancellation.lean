import Mathlib.Analysis.Complex.Basic
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteWindow_norm_sum_cancel_volume {V : Type*} (window : Finset V)
    (F : V → ℂ) (D : V → ℝ) {volume c C A E : ℝ}
    (hvolume : 0 < volume) (hc0 : 0 ≤ c) (hA : 0 ≤ A)
    (hD : ∀ v ∈ window, 0 ≤ D v)
    (hc : c ≤ C / volume) (hmass : (∑ v ∈ window, D v) / volume ≤ E)
    (hpoint : ∀ v ∈ window, ‖F v‖ ≤ c * (A * D v)) :
    (∑ v ∈ window, ‖F v‖) ≤ C * A * E := by
  have hE : 0 ≤ E := (div_nonneg (Finset.sum_nonneg hD) hvolume.le).trans hmass
  calc
    _ ≤ ∑ v ∈ window, c * (A * D v) := Finset.sum_le_sum hpoint
    _ = c * A * ∑ v ∈ window, D v := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ c * A * (E * volume) := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hvolume).mp hmass) (mul_nonneg hc0 hA)
    _ = (c * volume) * (A * E) := by ring
    _ ≤ C * (A * E) := mul_le_mul_of_nonneg_right
      ((le_div_iff₀ hvolume).mp hc) (mul_nonneg hA hE)
    _ = C * A * E := by ring

theorem finiteProbability_window_error {I V : Type*} [Fintype I]
    (weights : I → ℝ) (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (window : Finset V) (F G : I → V → ℂ) {E : ℝ}
    (herr : ∀ i, (∑ v ∈ window, ‖F i v - G i v‖) ≤ E) :
    ‖(∑ i, (weights i : ℂ) * ∑ v ∈ window, F i v) -
      ∑ i, (weights i : ℂ) * ∑ v ∈ window, G i v‖ ≤ E := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, weights i * E := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (herr i)) (hw i)
    _ = E := by rw [← Finset.sum_mul, hsum, one_mul]

end Erdos3

end

end OAI
