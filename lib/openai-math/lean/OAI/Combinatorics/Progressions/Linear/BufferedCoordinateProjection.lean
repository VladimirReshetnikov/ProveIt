import OAI.Combinatorics.Progressions.Geometry.NormalizedCoordinateCutoff
import OAI.Combinatorics.Progressions.Linear.CoordinateZeroProjection

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]
variable (r : ℝ≥0) (hr : 0 < r) (f : (D → ℝ) → ℂ)

noncomputable def bufferedCoordinateProjection (z : D → ℝ) : ℂ :=
  (normalizedCoordinateCutoff D r hr z : ℂ) * f (coordinateZeroProjection P z)

theorem bufferedCoordinateProjection_norm_le (hf : ∀ z, ‖f z‖ ≤ 1) (z : D → ℝ) :
    ‖bufferedCoordinateProjection P r hr f z‖ ≤ 1 := by
  have hc := (normalizedCoordinateCutoff_spec D r hr).2.2.1 z
  rw [bufferedCoordinateProjection, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc.1]
  exact (mul_le_mul hc.2 (hf _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem bufferedCoordinateProjection_lipschitz {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    LipschitzWith (L + Fintype.card D * normalizedSiteCutoffBound / (2 * r))
      (bufferedCoordinateProjection P r hr f) := by
  have hc := normalizedCoordinateCutoff_spec D r hr
  have hcLip : LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r))
      (fun z => (normalizedCoordinateCutoff D r hr z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact hc.2.2.2.2.2.dist_le_mul z w
  have hc1 (z : D → ℝ) : ‖(normalizedCoordinateCutoff D r hr z : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc.2.2.1 z).1]
    exact (hc.2.2.1 z).2
  have h := lipschitz_mul_of_bounds _ _ hcLip (hf.comp (coordinateZeroProjection_lipschitz P))
    (Bf := 1) (Bg := 1) hc1 (fun z => hf1 (coordinateZeroProjection P z))
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [bufferedCoordinateProjection, Function.comp_def, one_mul, mul_one] using h.dist_le_mul z w

theorem bufferedCoordinateProjection_hasCompactSupport :
    HasCompactSupport (bufferedCoordinateProjection P r hr f) := by
  have hc : HasCompactSupport (fun z => (normalizedCoordinateCutoff D r hr z : ℂ)) :=
    (normalizedCoordinateCutoff_spec D r hr).2.1.comp_left Complex.ofReal_zero
  exact hc.mul_right

theorem bufferedCoordinateProjection_eq (z : D → ℝ) (hz : ∀ d, |z d| ≤ (r : ℝ)) :
    bufferedCoordinateProjection P r hr f z = f (coordinateZeroProjection P z) := by
  rw [bufferedCoordinateProjection, (normalizedCoordinateCutoff_spec D r hr).2.2.2.1 z hz,
    Complex.ofReal_one, one_mul]

theorem bufferedCoordinateProjection_nonzero_box (z : D → ℝ)
    (hz : bufferedCoordinateProjection P r hr f z ≠ 0) : ∀ d, |z d| ≤ 2 * (r : ℝ) := by
  apply (normalizedCoordinateCutoff_spec D r hr).2.2.2.2.1 z
  intro hc
  apply hz
  rw [bufferedCoordinateProjection, hc, Complex.ofReal_zero, zero_mul]

end Erdos3

end

end OAI
