import OAI.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
import OAI.Combinatorics.Progressions.Sampling.L1SamplingSurrogate

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped Classical BigOperators NNReal

theorem selectedResidueDensityMass_l1_surrogate
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {K I : Type*} [Fintype K] [Fintype I]
    (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (s : (K × I → ℤ) → X) (f ideal g : X → ℂ)
    (hf : Measurable f) (hi : Measurable ideal) (hg : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Cf) (hgb : ∀ x, ‖g x‖ ≤ Cg)
    {E δ ε : ℝ} (happrox : ∀ x, ‖ideal x - g x‖ ≤ δ)
    (hmass : (∫ x, ‖f x - ideal x‖ ∂μ) ≤ E)
    (hsample : selectedResidueDensityMass stride cells V
      (fun z => ‖f (s z) - g (s z)‖) ≤ (∫ x, ‖f x - g x‖ ∂μ) + ε) :
    selectedResidueDensityMass stride cells V
      (fun z => ‖f (s z) - ideal (s z)‖) ≤ E + 2 * δ + ε := by
  let ν := (selectedResidueSmoothPMF stride cells V hV hZ).toMeasure
  have hib (x) : ‖ideal x‖ ≤ δ + Cg := by
    calc
      _ ≤ ‖ideal x - g x‖ + ‖g x‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add (happrox x) (hgb x)
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable Cf (Filter.Eventually.of_forall hfb)
  have hii : Integrable ideal μ := Integrable.of_bound hi.aestronglyMeasurable (δ + Cg) (Filter.Eventually.of_forall hib)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable Cg (Filter.Eventually.of_forall hgb)
  have hfs : Integrable (fun z => f (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable Cf (Filter.Eventually.of_forall (fun z => hfb _))
  have his : Integrable (fun z => ideal (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable (δ + Cg) (Filter.Eventually.of_forall (fun z => hib _))
  have hgs : Integrable (fun z => g (s z)) ν := Integrable.of_bound
    (measurable_of_countable _).aestronglyMeasurable Cg (Filter.Eventually.of_forall (fun z => hgb _))
  have hs' : (∫ z, ‖f (s z) - g (s z)‖ ∂ν) ≤ (∫ x, ‖f x - g x‖ ∂μ) + ε := by
    exact (selectedResidueDensityMass_integral stride cells V hV hZ _ (hfs.sub hgs).norm).symm.trans_le hsample
  exact (selectedResidueDensityMass_integral stride cells V hV hZ _ (hfs.sub his).norm).trans_le
    (l1_sampling_via_uniform_surrogate μ ν s f ideal g hfi hii hgi hfs his hgs happrox hmass hs')

end Erdos3

end

end OAI
