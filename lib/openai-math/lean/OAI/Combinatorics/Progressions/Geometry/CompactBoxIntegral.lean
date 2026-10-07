import Mathlib.MeasureTheory.Function.LocallyIntegrable
import OAI.Combinatorics.Progressions.Lattices.RectangularLatticeCells

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {J : Type*} [Fintype J]

theorem compactBox_integrable (f : (J → ℝ) → ℝ) (hf : Continuous f) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hx (hsupport x h)

theorem integral_norm_le_box (f : (J → ℝ) → ℝ) {R C : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ x, R < ‖x‖ → f x = 0) (hbound : ∀ x, ‖x‖ ≤ R → ‖f x‖ ≤ C) :
    (∫ x, ‖f x‖) ≤ C * (2 * R) ^ Fintype.card J := by
  let s := Metric.closedBall (0 : J → ℝ) R
  have hs : MeasurableSet s := measurableSet_closedBall
  have hi : Integrable (s.indicator (fun _ : J → ℝ => C)) :=
    (integrableOn_const ((isCompact_closedBall (0 : J → ℝ) R).measure_lt_top.ne)).integrable_indicator hs
  have hb : ∀ x, ‖f x‖ ≤ s.indicator (fun _ : J → ℝ => C) x := by
    intro x
    by_cases hx : x ∈ s
    · have hx' : ‖x‖ ≤ R := by simpa only [s, Metric.mem_closedBall, dist_zero_right] using hx
      simpa only [Set.indicator_of_mem hx] using hbound x hx'
    · have hx' : R < ‖x‖ := by simpa only [s, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      simp only [hzero x hx', norm_zero, Set.indicator_of_notMem hx, le_refl]
  have hv : volume.real s = (2 * R) ^ Fintype.card J := by
    rw [measureReal_def, Real.volume_pi_closedBall 0 hR, ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ ∫ x, s.indicator (fun _ : J → ℝ => C) x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hi
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_indicator_const C hs, hv, smul_eq_mul]; ring

end Erdos3

end

end OAI
