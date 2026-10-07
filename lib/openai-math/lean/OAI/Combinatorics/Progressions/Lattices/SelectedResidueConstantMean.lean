import OAI.Combinatorics.Progressions.Lattices.SelectedResidueApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothPMF_discard_error {K I J : Type*}
    [Fintype K] [Fintype I] [Fintype J]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w : (K × I → ℤ) → ℂ) (c : J → ℂ) (u : J → (K × I → ℤ) → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * ∑ j, c j * u j x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  simp_rw [selectedResidueSmoothPMF_toReal] at hdiscard ⊢
  exact normalized_finite_weight_discard_error _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ w c u keep hc hτ hdiscard

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueSmoothPMF_const {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (c : ℂ) :
    (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * c) = c := by
  simp_rw [selectedResidueSmoothPMF_toReal]
  rw [← finiteSupportProbability_complexMean _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ (fun _ => c)]
  exact FiniteProbabilityWeights.complexMean_const _ c

end Erdos3

end

end OAI
