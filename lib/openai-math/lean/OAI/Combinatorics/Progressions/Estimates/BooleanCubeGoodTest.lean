import OAI.Combinatorics.Progressions.Probability.BooleanCubeGoodMass

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem booleanCubeGoodWeight_integral_test {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (ψ : ℝ → ℝ)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ)
    (f : (BlockParameter B (Fin h) α → ℝ) → ℝ) :
    (∫ a, booleanCubeGoodWeight c sets block v sel ψ r κ a * f a) =
      ∫ x, goodDomainCutoff ψ κ
        (fun j => booleanCubeDeterminant (c j) sets (block j) v (sel j))
        (scalarCubeProductCutoff α r) x * f (blockCubeFlatten B (Fin h) α x)
        ∂scalarCubeProductMeasure (B × Fin h) α := by
  unfold booleanCubeGoodWeight
  rw [blockCubeWeight_integral_test]
  exact scalarCubeGoodWeight_integral_test ψ r hr κ _ _

theorem booleanCubeGoodWeight_test_error {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (f : (BlockParameter B (Fin h) α → ℝ) → ℝ) (hf : Measurable f)
    (hbound : ∀ a, ‖f a‖ ≤ 1) :
    |(∫ a, f a ∂blockCubeMeasure B (Fin h) α) -
        ∫ a, booleanCubeGoodWeight c sets block v sel ψ r κ a * f a| ≤
      scalarCubeBoundaryConstant α * ∑ i, r i +
        ∑ j, (blockCubeMeasure B (Fin h) α).real
          {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) a| < 2 * κ j} := by
  let μ := scalarCubeProductMeasure (B × Fin h) α
  let d := fun j => booleanCubeDeterminant (c j) sets (block j) v (sel j)
  let b := scalarCubeProductCutoff α r
  let χ := goodDomainCutoff ψ κ d b
  have hd := fun j => booleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j)
  have hb : ContDiff ℝ ∞ b := scalarCubeProductCutoff_smooth r
  have hbr : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1 := scalarCubeProductCutoff_range r
  have hχm : Measurable χ := (goodDomainCutoff_smooth ψ hψ κ d hd b hb).continuous.measurable
  have hχr : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := goodDomainCutoff_range ψ hrange κ d b hbr
  have htest := mappedTest_cutoff_error μ χ hχm hχr (blockCubeFlatten B (Fin h) α)
    (blockCubeFlatten B (Fin h) α).continuous.measurable f hf hbound
  change |(∫ x, f (blockCubeFlatten B (Fin h) α x) ∂μ) -
    ∫ x, f (blockCubeFlatten B (Fin h) α x) ∂realDensityMeasure μ χ| ≤ _ at htest
  rw [realDensityMeasure_integral μ χ hχm (fun x => (hχr x).1)] at htest
  rw [blockCubeMeasure_integral, booleanCubeGoodWeight_integral_test c sets block v sel ψ r hr]
  apply htest.trans
  have hloss := goodDomainCutoff_integral_loss_le μ ψ hψ.continuous.measurable hrange hone
    κ hκ d (fun j => (hd j).continuous.measurable) b hb.continuous.measurable hbr
  have hboundary := scalarCubeProductCutoff_mass_loss (α := α) r hr
  have htotal := hloss.trans (add_le_add hboundary le_rfl)
  change (∫ x, 1 - χ x ∂μ) ≤ scalarCubeBoundaryConstant α * ∑ i, r i +
    ∑ j, (scalarCubeProductMeasure (B × Fin h) α).real
      {x | |booleanCubeDeterminant (c j) sets (block j) v (sel j) x| < 2 * κ j} at htotal
  simp_rw [booleanCubeDeterminant_sublevel_probability] at htotal
  exact htotal

end Erdos3

end

end OAI
