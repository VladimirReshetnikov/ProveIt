import OAI.Combinatorics.Progressions.Estimates.CircleFejerAverage

namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {X : Type*} [AddAction Circle X]

noncomputable def circleFourierComponent (n : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ t : Circle, character ((-n) • t) * f (t +ᵥ x) ∂circleHaar

theorem circleFourierComponent_vadd (n : ℤ) (f : X → ℂ) (a : Circle) (x : X) :
    circleFourierComponent n f (a +ᵥ x) = character (n • a) * circleFourierComponent n f x := by
  unfold circleFourierComponent
  calc
    _ = ∫ t : Circle, character (n • a) *
        (character ((-n) • (t + a)) * f ((t + a) +ᵥ x)) ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← add_vadd]
      have hchar : character ((-n) • t) = character (n • a) * character ((-n) • (t + a)) := by
        rw [← character_add]
        congr 1
        simp only [smul_add, neg_smul]
        abel
      rw [hchar, mul_assoc]
    _ = character (n • a) * ∫ t : Circle,
        character ((-n) • (t + a)) * f ((t + a) +ᵥ x) ∂circleHaar := integral_const_mul _ _
    _ = _ := by rw [integral_add_right_eq_self
      (fun t : Circle => character ((-n) • t) * f (t +ᵥ x)) a]

theorem norm_circleFourierComponent_le (n : ℤ) (f : X → ℂ) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖circleFourierComponent n f x‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg (character ((-n) • t) * f (t +ᵥ x))))
    (integrable_const B) (ae_of_all circleHaar (fun t : Circle => by
      simpa only [norm_mul, norm_character, one_mul] using hB (t +ᵥ x)))
  simpa using h

variable [TopologicalSpace X] [ContinuousVAdd Circle X]

theorem integrable_circleFourierComponent (n : ℤ) {f : X → ℂ} (hf : Continuous f) (x : X) :
    Integrable (fun t : Circle => character ((-n) • t) * f (t +ᵥ x)) circleHaar := by
  exact circle_integrable_of_continuous
    ((fourier (-n)).continuous.mul (hf.comp (continuous_id.vadd continuous_const)))

omit [TopologicalSpace X] [ContinuousVAdd Circle X] in
theorem circleFourierComponent_inherits_character (n : ℤ) {f : X → ℂ}
    (a : Circle) (z : ℂ) (ha : ∀ x, f (a +ᵥ x) = z * f x) (x : X) :
    circleFourierComponent n f (a +ᵥ x) = z * circleFourierComponent n f x := by
  unfold circleFourierComponent
  calc
    _ = ∫ t : Circle, z * (character ((-n) • t) * f (t +ᵥ x)) ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← add_vadd, add_comm t a, add_vadd, ha]
      ring
    _ = _ := integral_const_mul _ _

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

theorem lipschitz_circleFourierComponent (n : ℤ) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (circleFourierComponent n f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  unfold circleFourierComponent
  rw [← integral_sub (integrable_circleFourierComponent n hf.continuous x)
    (integrable_circleFourierComponent n hf.continuous y)]
  apply (norm_integral_le_integral_norm _).trans
  have hpoint (t : Circle) :
      ‖character ((-n) • t) * f (t +ᵥ x) - character ((-n) • t) * f (t +ᵥ y)‖ ≤
        (L : ℝ) * dist x y := by
    rw [← mul_sub, norm_mul, norm_character, one_mul, ← dist_eq_norm]
    exact (hf.dist_le_mul _ _).trans_eq (by rw [(hact t).dist_eq])
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg
      (character ((-n) • t) * f (t +ᵥ x) - character ((-n) • t) * f (t +ᵥ y))))
    (integrable_const ((L : ℝ) * dist x y)) (ae_of_all circleHaar hpoint)
  simpa using h

end Erdos3.CircleFourier

end

end OAI
