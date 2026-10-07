import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem haar_mixed_center_integral {Ω G : Type*} [MeasurableSpace Ω]
    [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (z : Ω → G) (hz : Measurable z)
    (φ : G → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ center, ∫ ω, φ (center + z ω) ∂ν ∂μ) = ∫ x, φ x ∂μ := by
  have hi : Integrable (fun p : G × Ω => φ (p.1 + z p.2)) (μ.prod ν) :=
    Integrable.of_bound (hφ.comp (measurable_fst.add (hz.comp measurable_snd))).aestronglyMeasurable
      C (ae_of_all _ (fun p => hbound _))
  rw [integral_integral_swap hi]
  simp only [integral_add_right_eq_self, integral_const, probReal_univ, one_smul]

end Erdos3

end

end OAI
