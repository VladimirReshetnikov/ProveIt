import OAI.Combinatorics.Progressions.Probability.DensityMixtureAELaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem retained_coefficient_density_average {W R X : Type*}
    [MeasurableSpace W] [MeasurableSpace R] [MeasurableSpace X]
    (μ : Measure W) (ρ : Measure R) (ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [SFinite ν]
    (D : R → X → ℝ) (hD : Measurable (Function.uncurry D))
    (hprob : ∀ r, (∀ x, 0 ≤ D r x) ∧ Integrable (D r) ν ∧ (∫ x, D r x ∂ν) = 1)
    (φ : W × X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p : (W × R) × X, D p.1.2 p.2*φ (p.1.1, p.2) ∂(μ.prod ρ).prod ν) =
      ∫ p : W × X, densityMixture ρ D p.2*φ p ∂μ.prod ν := by
  have hD' : Measurable (fun p : (W × R) × X => D p.1.2 p.2) :=
    hD.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hj := densityMixture_joint_integrable (μ.prod ρ) ν (fun wr => D wr.2) hD'
    (Filter.Eventually.of_forall (fun wr => hprob wr.2))
  have hi : Integrable (fun p : (W × R) × X => D p.1.2 p.2*φ (p.1.1, p.2)) ((μ.prod ρ).prod ν) :=
    hj.mul_bdd (hφ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (p.1.1, p.2)))
  have havg := densityMixture_probability_density ρ ν D hD (Filter.Eventually.of_forall hprob)
  have hmavg : Measurable (densityMixture ρ D) := hD.stronglyMeasurable.integral_prod_left'.measurable
  have hiavg := densityMixture_joint_integrable μ ν (fun _ : W => densityMixture ρ D)
    (hmavg.comp measurable_snd) (Filter.Eventually.of_forall (fun _ => havg))
  have hr : Integrable (fun p : W × X => densityMixture ρ D p.2*φ p) (μ.prod ν) :=
    hiavg.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left, integral_prod _ hr]
  apply integral_congr_ae
  filter_upwards [] with w
  exact (densityMixture_test_integral ρ ν D
    (densityMixture_joint_integrable ρ ν D hD (Filter.Eventually.of_forall hprob))
    (fun x => φ (w, x)) (hφ.comp (measurable_const.prodMk measurable_id)) (fun x => hbound (w, x))).symm

end Erdos3

end

end OAI
