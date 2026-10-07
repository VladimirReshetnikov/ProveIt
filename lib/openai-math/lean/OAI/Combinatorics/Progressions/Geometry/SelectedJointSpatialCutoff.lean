import OAI.Combinatorics.Progressions.Estimates.SelectedJointWeightedReferenceComparison
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueCutoffDomination

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedJointFiniteLaw_spatial_cutoff_bound
    {B K I : Type*} [Fintype K] [Fintype I]
    (bases : Finset B) (hbases : bases.Nonempty)
    (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
    (V : K × I → ℝ) (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass bases q T V D)
    (F : (K × I → ℝ) → ℝ) (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (small large : (K × I → ℤ) → Prop)
    (hcut : ∀ z, ‖fun t => (z t : ℝ) / V t‖ ≤ 1 →
      (if small z then (1 : ℝ) else 0) ≤ F (fun t => (z t : ℝ) / V t) ∧
      F (fun t => (z t : ℝ) / V t) ≤ if large z then 1 else 0)
    {ε η δ : ℝ}
    (hprior : (((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (large z))) true).toReal ≤ δ)
    (hmass : ∀ a, |selectedResidueDensityMass q T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
        (F (fun t => (z t : ℝ) / V t) * D a z)) -
        ∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
          F (fun t => (z t : ℝ) / V t)| ≤ ε) :
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).mean
      (fun z => if small z.2.val then (1 : ℝ) else 0) ≤ δ + (η + ε) := by
  have hdom := FiniteProbabilityWeights.mean_mono_positive_support
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD)
    (f := fun z => if small z.2.val then (1 : ℝ) else 0)
    (g := fun z => F (fun t => (z.2.val t : ℝ) / V t))
    (fun z hz => (hcut z.2.val
      (selectedJointFiniteLaw_normalized_norm_le q T V bases hbases hV hZ D hD0 hD z hz)).1)
  have hcmp := selectedJointFiniteLaw_weighted_reference_real_comparison
    bases hbases q T V hV hZ D hD0 hD
    (fun _ z => F (fun t => (z t : ℝ) / V t))
    (fun _ z => by rw [abs_of_nonneg (hF _).1]; exact (hF _).2) hmass htest
  have href : (selectedJointReference bases hbases q T V hV hZ).mean
      (fun z => F (fun t => (z.2.val t : ℝ) / V t)) =
      (selectedResidueFiniteLaw q T V hV hZ).mean
        (fun z => F (fun t => (z.val t : ℝ) / V t)) := by
    change ((FiniteProbabilityWeights.uniformFinset bases hbases).prod
      (selectedResidueFiniteLaw q T V hV hZ)).mean _ = _
    rw [FiniteProbabilityWeights.mean_prod]
    dsimp only
    rw [FiniteProbabilityWeights.mean_const]
  rw [href] at hcmp
  have hp := (selectedResidueFiniteLaw_cutoff_le_event q T V hV hZ F large
    (fun z hz => (hcut z hz).2)).trans hprior
  linarith [(abs_le.mp hcmp).2]

end Erdos3

end

end OAI
