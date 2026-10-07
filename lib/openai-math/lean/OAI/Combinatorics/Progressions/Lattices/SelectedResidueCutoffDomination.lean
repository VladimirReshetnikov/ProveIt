import OAI.Combinatorics.Progressions.Geometry.SelectedCenteredJointSupport
import OAI.Combinatorics.Progressions.Probability.MixedSelectedCoefficientProbability

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
variable (V : K × I → ℝ)

theorem selectedResidueSmoothWeight_normalized_norm_le (z : K × I → ℤ)
    (hz : selectedResidueSmoothWeight q T V z ≠ 0) :
    ‖fun t => (z t : ℝ) / V t‖ ≤ 1 := by
  by_contra! hn
  have hp := smoothProductProfile_zero_outside (K × I) (fun t => (z t : ℝ) / V t) hn
  exact hz (by simp [selectedResidueSmoothWeight, hp])

theorem selectedResidueSmoothPMF_normalized_norm_le_of_pos (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z) (z : K × I → ℤ)
    (hz : 0 < (selectedResidueSmoothPMF q T V hV hZ z).toReal) :
    ‖fun t => (z t : ℝ) / V t‖ ≤ 1 := by
  apply selectedResidueSmoothWeight_normalized_norm_le q T V z
  intro he
  rw [selectedResidueSmoothPMF_toReal, he, zero_div] at hz
  exact (lt_irrefl 0) hz

theorem selectedResidueFiniteLaw_normalized_norm_le (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (z : rectangularWeightIndices 0 V 1)
    (hz : 0 < (selectedResidueFiniteLaw q T V hV hZ).weight z) :
    ‖fun t => (z.val t : ℝ) / V t‖ ≤ 1 := by
  apply selectedResidueSmoothWeight_normalized_norm_le q T V z.val
  intro he
  change 0 < selectedResidueSmoothWeight q T V z.val /
    (∑' x, selectedResidueSmoothWeight q T V x) at hz
  rw [he, zero_div] at hz
  exact (lt_irrefl 0) hz

theorem selectedJointFiniteLaw_normalized_norm_le {A : Type*}
    (bases : Finset A) (hbases : bases.Nonempty) (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (D : A → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass bases q T V D)
    (z : bases × rectangularWeightIndices 0 V 1)
    (hz : 0 < (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).weight z) :
    ‖fun t => (z.2.val t : ℝ) / V t‖ ≤ 1 := by
  apply selectedResidueSmoothWeight_normalized_norm_le q T V z.2.val
  intro he
  rw [selectedJointFiniteLaw_weight, selectedResidueSmoothPMF_toReal, he, zero_div,
    mul_zero, zero_mul, zero_div] at hz
  exact (lt_irrefl 0) hz

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem mean_mono_positive_support {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) {f g : X → ℝ}
    (h : ∀ x, 0 < p.weight x → f x ≤ g x) : p.mean f ≤ p.mean g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < p.weight x
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)
  · have hz : p.weight x = 0 := le_antisymm (le_of_not_gt hx) (p.nonneg x)
    simp only [hz, zero_mul, le_refl]

end FiniteProbabilityWeights

variable {K I : Type*} [Fintype K] [Fintype I]
variable (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
variable (V : K × I → ℝ) (hV : ∀ t, 0 < V t)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)

theorem selectedResidueFiniteLaw_event_eq_map_true (bad : (K × I → ℤ) → Prop) :
    (selectedResidueFiniteLaw q T V hV hZ).eventProbability (fun z => bad z.val) =
      (((selectedResidueSmoothPMF q T V hV hZ).map (fun z => decide (bad z))) true).toReal := by
  have hoff (z : K × I → ℤ) (hz : z ∉ rectangularWeightIndices 0 V 1) :
      (selectedResidueSmoothPMF q T V hV hZ z).toReal = 0 := by
    rw [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight_zero_off q T V hV z hz, zero_div]
  calc
    _ = (FiniteProbabilityWeights.ofSupportedPMF (selectedResidueSmoothPMF q T V hV hZ)
        (rectangularWeightIndices 0 V 1) hoff).eventProbability (fun z => bad z.val) := by
      unfold FiniteProbabilityWeights.eventProbability FiniteProbabilityWeights.mean
      apply Finset.sum_congr rfl
      intro z _
      change selectedResidueSmoothWeight q T V z.val / _ * _ =
        (selectedResidueSmoothPMF q T V hV hZ z.val).toReal * _
      rw [selectedResidueSmoothPMF_toReal]
    _ = _ := supportedPMF_event_eq_map_true _ _ hoff bad

theorem selectedResidueFiniteLaw_cutoff_le_event
    (F : (K × I → ℝ) → ℝ) (bad : (K × I → ℤ) → Prop)
    (hF : ∀ z : K × I → ℤ, ‖fun t => (z t : ℝ) / V t‖ ≤ 1 →
      F (fun t => (z t : ℝ) / V t) ≤ if bad z then 1 else 0) :
    (selectedResidueFiniteLaw q T V hV hZ).mean
        (fun z => F (fun t => (z.val t : ℝ) / V t)) ≤
      (((selectedResidueSmoothPMF q T V hV hZ).map (fun z => decide (bad z))) true).toReal := by
  rw [← selectedResidueFiniteLaw_event_eq_map_true]
  apply FiniteProbabilityWeights.mean_mono_positive_support
  intro z hz
  exact hF z.val (selectedResidueFiniteLaw_normalized_norm_le q T V hV hZ z hz)

end Erdos3

end

end OAI
