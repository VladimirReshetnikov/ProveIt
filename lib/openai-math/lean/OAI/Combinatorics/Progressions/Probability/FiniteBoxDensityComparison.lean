import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem normalized_box_density_l1 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S) (hfinite : μ S < ∞)
    (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g) (hfi : Integrable f μ)
    (hf0 : ∀ x ∉ S, f x = 0) (hg0 : ∀ x ∉ S, g x = 0)
    {Q V ε : ℝ} (hQ : 0 < Q) (hε : 0 ≤ ε)
    (hvolume : μ.real S ≤ V*Q) (he : ∀ x, |Q*f x-g x| ≤ ε) :
    Integrable (fun x => g x/Q) μ ∧ (∫ x, |f x-g x/Q| ∂μ) ≤ V*ε := by
  let d := fun x => f x-g x/Q
  have hp (x) : |d x| ≤ ε/Q := by
    have hx : d x = (Q*f x-g x)/Q := by dsimp [d]; field_simp [hQ.ne']
    rw [hx, abs_div, abs_of_pos hQ]
    exact div_le_div_of_nonneg_right (he x) hQ.le
  have hbound (x) : ‖d x‖ ≤ S.indicator (fun _ => ε/Q) x := by
    by_cases hx : x ∈ S
    · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs] using hp x
    · simp only [Set.indicator_of_notMem hx, d, hf0 x hx, hg0 x hx, zero_div, sub_self, norm_zero, le_refl]
  have hmajor : Integrable (S.indicator (fun _ : X => ε/Q)) μ :=
    (integrableOn_const hfinite.ne).integrable_indicator hS
  have hdi : Integrable d μ :=
    hmajor.mono' (hfm.sub (hgm.div_const Q)).aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hgi : Integrable (fun x => g x/Q) μ := by
    convert hfi.sub hdi using 1
    ext x
    dsimp [d]
    ring
  refine ⟨hgi, ?_⟩
  calc
    _ = ∫ x, ‖d x‖ ∂μ := by simp only [d, Real.norm_eq_abs]
    _ ≤ ∫ x, S.indicator (fun _ : X => ε/Q) x ∂μ :=
      integral_mono hdi.norm hmajor hbound
    _ = (ε/Q)*μ.real S := by rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]
    _ ≤ (ε/Q)*(V*Q) := mul_le_mul_of_nonneg_left hvolume (div_nonneg hε hQ.le)
    _ = V*ε := by field_simp [hQ.ne']

end Erdos3

end

end OAI
