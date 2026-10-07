import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_l1_le_of_complex_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℂ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      ‖(∫ x, (f x : ℂ) * φ x ∂μ) - (∫ x, (g x : ℂ) * φ x ∂μ)‖ ≤ ε) :
    (∫ x, |f x - g x| ∂μ) ≤ ε := by
  apply density_l1_le_of_bounded_tests μ f g hf hg hfi hgi
  intro φ hφ hb
  have h := he (fun x => (φ x : ℂ)) hφ.complex_ofReal
    (fun x => by simpa only [Complex.norm_real] using hb x)
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

theorem density_l1_triangle_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x - h x| ∂μ) ≤ (∫ x, |f x - g x| ∂μ) + ∫ x, |g x - h x| ∂μ := by
  rw [← integral_add (f := fun x => |f x - g x|) (g := fun x => |g x - h x|)
    (hf.sub hg).abs (hg.sub hh).abs]
  exact integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
    (fun x => abs_sub_le (f x) (g x) (h x))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem density_l1_triangle_bound_reverse {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    {A B : ℝ} (hfg : (∫ x, |f x - g x| ∂μ) ≤ A)
    (hhg : (∫ x, |h x - g x| ∂μ) ≤ B) :
    (∫ x, |f x - h x| ∂μ) ≤ A + B := by
  apply (density_l1_triangle_le μ f g h hf hg hh).trans
  apply add_le_add hfg
  simpa only [abs_sub_comm] using hhg

end Erdos3

end

end OAI
