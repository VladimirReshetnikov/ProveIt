import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def linearCutoff (a : ℝ) (h : ℝ≥0) (t : ℝ) : ℝ :=
  max 0 (min 1 ((a + (h : ℝ) - t) / h))

theorem linearCutoff_range (a : ℝ) (h : ℝ≥0) (t : ℝ) :
    0 ≤ linearCutoff a h t ∧ linearCutoff a h t ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem linearCutoff_eq_one (a : ℝ) (h : ℝ≥0) (hh : 0 < h) {t : ℝ} (ht : t ≤ a) :
    linearCutoff a h t = 1 := by
  have hhR : (0 : ℝ) < h := hh
  have hfrac : (1 : ℝ) ≤ (a + (h : ℝ) - t) / h := (le_div_iff₀ hhR).mpr (by linarith)
  simp only [linearCutoff, min_eq_left hfrac, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem linearCutoff_eq_zero (a : ℝ) (h : ℝ≥0) {t : ℝ} (ht : a + (h : ℝ) ≤ t) :
    linearCutoff a h t = 0 := by
  have hfrac : (a + (h : ℝ) - t) / h ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) h.coe_nonneg
  exact max_eq_left ((min_le_right _ _).trans hfrac)

theorem linearCutoff_mono_center {a b : ℝ} (hab : a ≤ b) (h : ℝ≥0) (t : ℝ) :
    linearCutoff a h t ≤ linearCutoff b h t := by
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  exact div_le_div_of_nonneg_right (by linarith) h.coe_nonneg

theorem linearCutoff_lipschitz (a : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    LipschitzWith h⁻¹ (linearCutoff a h) := by
  have hhR : (0 : ℝ) < h := hh
  have haff : LipschitzWith h⁻¹ (fun t : ℝ => (a + (h : ℝ) - t) / h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, ← sub_div]
    have heq : (a + (h : ℝ) - x) - (a + (h : ℝ) - y) = -(x - y) := by ring
    rw [heq, abs_div, abs_neg, abs_of_pos hhR]
    simp only [NNReal.coe_inv]
    exact le_of_eq (by ring)
  exact (haff.const_min 1).const_max 0

end Erdos3

end

end OAI
