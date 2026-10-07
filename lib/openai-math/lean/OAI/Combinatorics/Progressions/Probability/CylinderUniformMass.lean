import OAI.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition

namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}

omit [∀ i, DecidableEq (X i)] in
theorem CylinderRemovalChain.size_le (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs) :
    ∀ d ∈ cs, d.1.card ≤ j := by
  induction hchain with
  | nil => simp
  | @cons w rem cs d hsize hmass hbounded rest ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hsize
    · exact ih c hc

theorem CylinderRemovalChain.removed_mass_le_two
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    {η : ℝ} (hη : η ≤ 1)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η j) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      cf.1.mass μ base (observedProductDensity μ p F cf.2) ≤ 2 := by
  intro cf hcf
  have hf := removedCylinderWeights_bounds F w cs (fun z => (hw z).1) (fun z => (hw z).2)
    (List.of_mem_zip hcf).2
  have hb := observedProductDensity_marginal_le μ p F hμ cf.2 (fun z => (hf z).2)
    hclose cf.1.1 (hchain.removed_size_mass cf hcf).1 (cf.1.assignment base)
  change productConditionalMean μ cf.1.1 (observedProductDensity μ p F cf.2) (cf.1.assignment base) ≤ 2
  linarith

end Erdos3

end

end OAI
