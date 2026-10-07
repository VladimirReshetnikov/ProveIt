import Mathlib.MeasureTheory.Function.LocallyIntegrable
import OAI.Combinatorics.Progressions.Lattices.RectangularLatticeCells

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem compactInterval_integrable (f : ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hsupport : ∀ x, R < |x| → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
  intro x hx
  apply abs_le.mp
  by_contra! h
  exact hx (hsupport x h)

theorem integral_norm_le_interval (f : ℝ → ℝ) {u v C : ℝ} (huv : u ≤ v)
    (hzero : ∀ x, x ∉ Set.Icc u v → f x = 0)
    (hbound : ∀ x ∈ Set.Icc u v, ‖f x‖ ≤ C) :
    (∫ x, ‖f x‖) ≤ C * (v - u) := by
  have hi : Integrable ((Set.Icc u v).indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (by simp : volume (Set.Icc u v) ≠ ⊤)).integrable_indicator measurableSet_Icc
  have hb : ∀ x, ‖f x‖ ≤ (Set.Icc u v).indicator (fun _ : ℝ => C) x := by
    intro x
    by_cases hx : x ∈ Set.Icc u v
    · simpa only [Set.indicator_of_mem hx] using hbound x hx
    · simp only [hzero x hx, norm_zero, Set.indicator_of_notMem hx, le_refl]
  calc
    _ ≤ ∫ x, (Set.Icc u v).indicator (fun _ : ℝ => C) x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hi
        (Filter.Eventually.of_forall hb)
    _ = C * (v - u) := by
      rw [integral_indicator_const C measurableSet_Icc, Real.volume_real_Icc_of_le huv, smul_eq_mul]
      ring

end Erdos3

end

end OAI
