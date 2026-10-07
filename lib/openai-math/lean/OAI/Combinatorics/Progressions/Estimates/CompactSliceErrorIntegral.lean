import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Geometry.CompactBoxIntegral

namespace OAI

section

namespace Erdos3
open MeasureTheory

variable {C J : Type*} [Fintype C] [Fintype J]

theorem compactProductDensity_integrable
    (g : (C → ℝ) × (J → ℝ) → ℝ) (hg : Continuous g) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    Integrable g ((volume : Measure (C → ℝ)).prod (volume : Measure (J → ℝ))) := by
  apply hg.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (C → ℝ) × (J → ℝ)) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  exact hx (hsupport x hn)

theorem compactSliceError_integral_norm_le
    (g : (C → ℝ) × (J → ℝ) → ℝ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) {R A B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (err : (C → ℝ) → ℂ) (herr0 : ∀ c, R < ‖c‖ → err c = 0)
    (herr : ∀ c, ‖c‖ ≤ R → ‖err c‖ ≤ A + B * ∫ x, g (c, x)) :
    (∫ c, ‖err c‖) ≤ A * (2 * R) ^ Fintype.card C +
      B * ∫ x, g x ∂((volume : Measure (C → ℝ)).prod (volume : Measure (J → ℝ))) := by
  let s := Metric.closedBall (0 : C → ℝ) R
  have hs : MeasurableSet s := measurableSet_closedBall
  have hi : Integrable (s.indicator (fun _ : C → ℝ => A)) :=
    (integrableOn_const ((isCompact_closedBall (0 : C → ℝ) R).measure_lt_top.ne)).integrable_indicator hs
  have hgi := compactProductDensity_integrable g hg R hsupport
  have hm : Integrable (fun c : C → ℝ => B * ∫ x, g (c, x)) :=
    hgi.integral_prod_left.const_mul B
  have hb (c : C → ℝ) :
      ‖err c‖ ≤ s.indicator (fun _ : C → ℝ => A) c + B * ∫ x, g (c, x) := by
    by_cases hc : c ∈ s
    · rw [Set.indicator_of_mem hc]
      exact herr c (by simpa only [s, Metric.mem_closedBall, dist_zero_right] using hc)
    · have hc' : R < ‖c‖ := by
        simpa only [s, Metric.mem_closedBall, dist_zero_right, not_le] using hc
      rw [herr0 c hc', norm_zero, Set.indicator_of_notMem hc, zero_add]
      exact mul_nonneg hB (integral_nonneg (fun x => hg0 (c, x)))
  have hv : volume.real s = (2 * R) ^ Fintype.card C := by
    rw [measureReal_def, Real.volume_pi_closedBall 0 hR, ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ ∫ c, s.indicator (fun _ : C → ℝ => A) c + B * ∫ x, g (c, x) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun c => norm_nonneg (err c)))
        (hi.add hm) (Filter.Eventually.of_forall hb)
    _ = _ := by
      rw [integral_add hi hm, integral_indicator_const A hs, hv,
        smul_eq_mul, integral_const_mul, ← integral_prod g hgi]
      ring

theorem compactSliceError_norm_integral_le
    (g : (C → ℝ) × (J → ℝ) → ℝ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) {R A B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (err : (C → ℝ) → ℂ) (herr0 : ∀ c, R < ‖c‖ → err c = 0)
    (herr : ∀ c, ‖c‖ ≤ R → ‖err c‖ ≤ A + B * ∫ x, g (c, x)) :
    ‖∫ c, err c‖ ≤ A * (2 * R) ^ Fintype.card C +
      B * ∫ x, g x ∂((volume : Measure (C → ℝ)).prod (volume : Measure (J → ℝ))) :=
  (norm_integral_le_integral_norm _).trans
    (compactSliceError_integral_norm_le g hg hg0 hR hB hsupport err herr0 herr)

end Erdos3

end

end OAI
