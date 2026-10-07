import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedResidueDensityPMF_normalizedDensityTest {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D) (f : (K × I → ℤ) → ℂ) :
    (∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z) =
      (selectedResidueFiniteLaw modulus T W hW hZ).normalizedDensityTest
        (fun z => D z.val) (fun z => f z.val) := by
  rw [selectedResidueDensityPMF_complexMean, FiniteProbabilityWeights.normalizedDensityTest,
    selectedResidueFiniteLaw_densityMass,
    selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => (D z : ℂ)*f z)]

theorem selectedResidue_center_mixture_compare {C K I : Type*} [MeasurableSpace C]
    [Fintype K] [Fintype I] (μ : Measure C) [IsProbabilityMeasure μ]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : C → (K × I → ℤ) → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z) (hD : ∀ c, 0 < selectedResidueDensityMass modulus T W (D c))
    (F : C → (K × I → ℤ) → ℝ) (hF : ∀ z, Integrable (fun c => F c z) μ)
    (hFmass : ∀ z, (∫ c, F c z ∂μ) = 1)
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (herror : ∀ c,
      ‖(∑' z, ((selectedResidueDensityPMF modulus T W hW hZ (D c) (hD0 c) (hD c) z).toReal : ℂ)*f z) -
        (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*(f z*(F c z : ℂ)))‖ ≤ ε) :
    ‖(∫ c, ∑' z, ((selectedResidueDensityPMF modulus T W hW hZ (D c) (hD0 c) (hD c) z).toReal : ℂ)*f z ∂μ) -
      (∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ)*f z)‖ ≤ ε := by
  simp_rw [selectedResidueDensityPMF_normalizedDensityTest]
  rw [← selectedResidueFiniteLaw_complexMean modulus T W hW hZ f]
  apply FiniteProbabilityWeights.integral_normalizedDensityTest_compare
    (selectedResidueFiniteLaw modulus T W hW hZ) μ
    (fun c z => D c z.val) (fun z => hDm z.val) (fun c z => hD0 c z.val)
    (fun c => by rw [selectedResidueFiniteLaw_densityMass]; exact hD c)
    (fun c z => F c z.val) (fun z => hF z.val) (fun z => hFmass z.val)
    (fun z => f z.val) (fun z => hf z.val)
  intro c
  have h := herror c
  rw [selectedResidueDensityPMF_normalizedDensityTest,
    ← selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => f z*(F c z : ℂ))] at h
  exact h

end Erdos3

end

end OAI
