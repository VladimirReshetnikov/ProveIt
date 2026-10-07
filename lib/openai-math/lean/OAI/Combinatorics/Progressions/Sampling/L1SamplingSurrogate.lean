import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem l1_sampling_via_uniform_surrogate
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Y → X) (f ideal g : X → ℂ)
    (hf : Integrable f μ) (hi : Integrable ideal μ) (hg : Integrable g μ)
    (hfs : Integrable (fun y => f (s y)) ν)
    (his : Integrable (fun y => ideal (s y)) ν)
    (hgs : Integrable (fun y => g (s y)) ν)
    {E δ ε : ℝ} (happrox : ∀ x, ‖ideal x - g x‖ ≤ δ)
    (hmass : (∫ x, ‖f x - ideal x‖ ∂μ) ≤ E)
    (hsample : (∫ y, ‖f (s y) - g (s y)‖ ∂ν) ≤
      (∫ x, ‖f x - g x‖ ∂μ) + ε) :
    (∫ y, ‖f (s y) - ideal (s y)‖ ∂ν) ≤ E + 2 * δ + ε := by
  have hhaar : (∫ x, ‖f x - g x‖ ∂μ) ≤ E + δ := by
    calc
      _ ≤ ∫ x, ‖f x - ideal x‖ + δ ∂μ :=
        integral_mono (hf.sub hg).norm ((hf.sub hi).norm.add (integrable_const δ))
          (fun x => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
            (add_le_add le_rfl (happrox x)))
      _ = (∫ x, ‖f x - ideal x‖ ∂μ) + δ := by
        simpa [Pi.sub_apply] using
          (integral_add (hf.sub hi).norm (integrable_const δ))
      _ ≤ E + δ := add_le_add hmass le_rfl
  calc
    _ ≤ ∫ y, ‖f (s y) - g (s y)‖ + δ ∂ν :=
      integral_mono (hfs.sub his).norm ((hfs.sub hgs).norm.add (integrable_const δ))
        (fun y => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
          (add_le_add le_rfl (by simpa only [norm_sub_rev] using happrox (s y))))
    _ = (∫ y, ‖f (s y) - g (s y)‖ ∂ν) + δ := by
      simpa [Pi.sub_apply] using
        (integral_add (hfs.sub hgs).norm (integrable_const δ))
    _ ≤ ((E + δ) + ε) + δ :=
      add_le_add (hsample.trans (add_le_add hhaar le_rfl)) le_rfl
    _ = _ := by ring

end Erdos3

end

end OAI
