/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedJointFiniteLaw_support {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (z : A × rectangularWeightIndices 0 W 1)
    (hz : 0 < (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).weight z) :
    columnResiduePattern modulus z.2.val ∈ T ∧ 0 < D z.1.val z.2.val := by
  rw [selectedJointFiniteLaw_weight] at hz
  constructor
  · by_contra h
    rw [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight, ite_eq_right h] at hz
    simp only [zero_div, mul_zero, zero_mul] at hz
    exact (lt_irrefl 0) hz
  · apply lt_of_le_of_ne (hD0 _ _)
    intro he
    rw [← he] at hz
    simp only [mul_zero, zero_div] at hz
    exact (lt_irrefl 0) hz

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped Classical

theorem selectedCenteredJointFiniteLaw_ae_support
    {C B K I : Type*} [MeasurableSpace C] [Fintype K] [Fintype I]
    (μ : Measure C) (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (D : C → B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus cells W (D c))
    [MeasurableSpace (A × rectangularWeightIndices 0 W 1)]
    [MeasurableSingletonClass (A × rectangularWeightIndices 0 W 1)]
    (hweight : ∀ z, Measurable (fun c =>
      (selectedJointFiniteLaw A hA modulus cells W hW hZ (D c) (hD0 c) (hD c)).weight z)) :
    ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ
      (fun c => selectedJointFiniteLaw A hA modulus cells W hW hZ (D c) (hD0 c) (hD c)),
      columnResiduePattern modulus z.2.2.val ∈ cells ∧
      0 < D z.1 z.2.1.val z.2.2.val := by
  apply (centeredFiniteProbabilityMeasure_ae_positive_weight μ
    (fun c => selectedJointFiniteLaw A hA modulus cells W hW hZ (D c) (hD0 c) (hD c))
    hweight).mono
  intro z hz
  exact selectedJointFiniteLaw_support A hA modulus cells W hW hZ
    (D z.1) (hD0 z.1) (hD z.1) z.2 hz

end Erdos3

end

end OAI
