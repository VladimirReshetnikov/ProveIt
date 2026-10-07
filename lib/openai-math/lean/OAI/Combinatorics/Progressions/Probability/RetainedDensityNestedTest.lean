import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem retained_density_nested_test_error {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f g : X → ℝ) (hf : Integrable f ν) (hg : Integrable g ν)
    (φ : Z × X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ p, ‖φ p‖ ≤ B) :
    ‖(∫ z, ∫ x, (f x : ℂ) * φ (z, x) ∂ν ∂μ) -
      ∫ z, ∫ x, (g x : ℂ) * φ (z, x) ∂ν ∂μ‖ ≤ B * ∫ x, |f x - g x| ∂ν := by
  have hfi := integrable_snd_probability μ ν f hf
  have hgi := integrable_snd_probability μ ν g hg
  have hF : Integrable (fun p : Z × X => (f p.2 : ℂ) * φ p) (μ.prod ν) :=
    hfi.ofReal.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hb)
  have hG : Integrable (fun p : Z × X => (g p.2 : ℂ) * φ p) (μ.prod ν) :=
    hgi.ofReal.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hb)
  rw [← integral_prod _ hF, ← integral_prod _ hG]
  have he := density_bounded_complex_test_error (μ.prod ν) (fun p => f p.2) (fun p => g p.2)
    hfi hgi φ hφ hb
  rwa [integral_snd_probability μ ν (fun x => |f x - g x|) (hf.sub hg).abs] at he

end Erdos3

end

end OAI
