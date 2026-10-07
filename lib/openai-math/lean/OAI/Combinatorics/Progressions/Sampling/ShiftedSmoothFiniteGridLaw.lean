/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem shiftedSmoothProductPMF_positive_coord_lt {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (k : I → ℤ) (hk : 0 < (shiftedSmoothProductPMF a S hS hZ k).toReal) (i : I) :
    |rectangularLatticePoint a S k i| < 3 / 4 := by
  by_contra hn
  have hz := smoothProbabilityProfile_zero (rectangularLatticePoint a S k i)
    (le_of_not_gt hn)
  have hp : smoothProductProfile I (rectangularLatticePoint a S k) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  rw [shiftedSmoothProductPMF_toReal] at hk
  change 0 < smoothProductProfile I (rectangularLatticePoint a S k) /
    shiftedSmoothProductMass a S at hk
  rw [hp, zero_div] at hk
  exact (lt_irrefl 0) hk

noncomputable def shiftedSmoothPositiveGrid {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    Finset (I → ℤ) :=
  (rectangularWeightIndices a S 1).filter
    (fun k => 0 < (shiftedSmoothProductPMF a S hS hZ k).toReal)

theorem shiftedSmoothPositiveGrid_zero_off {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (k : I → ℤ) (hk : k ∉ shiftedSmoothPositiveGrid a S hS hZ) :
    (shiftedSmoothProductPMF a S hS hZ k).toReal = 0 := by
  by_cases hmem : k ∈ rectangularWeightIndices a S 1
  · have hnot : ¬ 0 < (shiftedSmoothProductPMF a S hS hZ k).toReal :=
      fun hpos => hk (Finset.mem_filter.mpr ⟨hmem, hpos⟩)
    exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
  · exact shiftedSmoothProductPMF_toReal_zero_off a S hS hZ k hmem

theorem shiftedSmoothPositiveGrid_coord_lt {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (k : I → ℤ) (hk : k ∈ shiftedSmoothPositiveGrid a S hS hZ) (i : I) :
    |rectangularLatticePoint a S k i| < 3 / 4 :=
  shiftedSmoothProductPMF_positive_coord_lt a S hS hZ k (Finset.mem_filter.mp hk).2 i

noncomputable def shiftedSmoothPositiveGridWeights {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    FiniteProbabilityWeights (shiftedSmoothPositiveGrid a S hS hZ) :=
  FiniteProbabilityWeights.ofSupportedPMF (shiftedSmoothProductPMF a S hS hZ)
    (shiftedSmoothPositiveGrid a S hS hZ) (shiftedSmoothPositiveGrid_zero_off a S hS hZ)

@[simp] theorem shiftedSmoothPositiveGridWeights_weight {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (k : shiftedSmoothPositiveGrid a S hS hZ) :
    (shiftedSmoothPositiveGridWeights a S hS hZ).weight k =
      (shiftedSmoothProductPMF a S hS hZ k.val).toReal := rfl

theorem shiftedSmoothPositiveGridWeights_weight_pos {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (k : shiftedSmoothPositiveGrid a S hS hZ) :
    0 < (shiftedSmoothPositiveGridWeights a S hS hZ).weight k :=
  (Finset.mem_filter.mp k.property).2

theorem shiftedSmoothPositiveGridWeights_event_eq_map_true {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (bad : (I → ℤ) → Prop) :
    (shiftedSmoothPositiveGridWeights a S hS hZ).eventProbability (fun k => bad k.val) =
      (((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide (bad k))) true).toReal := by
  have h := FiniteProbabilityWeights.ofSupportedPMF_map_event
    (shiftedSmoothProductPMF a S hS hZ) (shiftedSmoothPositiveGrid a S hS hZ)
    (shiftedSmoothPositiveGrid_zero_off a S hS hZ) (fun k => decide (bad k))
    (fun b : Bool => b = true)
  simpa [shiftedSmoothPositiveGridWeights, FiniteProbabilityWeights.eventProbability,
    FiniteProbabilityWeights.mean] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem rectangularWeightIndices_normalized_bound {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i)
    (k : rectangularWeightIndices a S 1) (i : I) :
    |rectangularLatticePoint a S k.val i| ≤ 1 := by
  have hi := Fintype.mem_piFinset.mp k.property i
  have h := sampledWeightIndices_mem_bound hi
  change |((k.val i : ℝ) - a i) / S i| ≤ 1
  rw [abs_div, abs_of_pos (hS i), div_le_one (hS i)]
  simpa only [mul_one] using h

theorem rectangularLatticePoint_injective {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    Function.Injective (rectangularLatticePoint a S) := by
  intro k l h
  funext i
  have hi := congrFun h i
  change ((k i : ℝ) - a i) / S i = ((l i : ℝ) - a i) / S i at hi
  have hi' := (div_left_inj' (hS i).ne').mp hi
  have he : (k i : ℝ) = (l i : ℝ) := by linarith
  exact_mod_cast he

theorem shiftedSmoothProductPMF_point_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i) (k : I → ℤ) :
    (shiftedSmoothProductPMF a S hS hZ k).toReal ≤
      (2 : ℝ) ^ Fintype.card I * (∏ i, S i)⁻¹ := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  calc
    _ ≤ ∏ i, 2 / S i := Finset.prod_le_prod₀
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun i _ => shiftedSmoothCoefficientPMF_le (a i) (hlarge i) (k i))
    _ = _ := by simp only [div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Finset.prod_inv_distrib]

theorem shiftedSmoothProductFiniteWeights_point_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (k : rectangularWeightIndices a S 1) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).weight k ≤
      (2 : ℝ) ^ Fintype.card I * (∏ i, S i)⁻¹ :=
  shiftedSmoothProductPMF_point_le a S hS hZ hlarge k.val

theorem shiftedSmoothProductFiniteWeights_mean_eq_tsum {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (I → ℤ) → ℝ) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).mean (fun k => f k.val) =
      ∑' k, (shiftedSmoothProductPMF a S hS hZ k).toReal * f k := by
  change (∑ k : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ k.val).toReal * f k.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun k => (shiftedSmoothProductPMF a S hS hZ k).toReal * f k)]
  exact (hasSum_sum_of_ne_finset_zero (fun k hk => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ k hk, zero_mul])).tsum_eq.symm

theorem shiftedSmoothProductFiniteWeights_event_eq_map {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (event : (I → ℤ) → Prop) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability (fun k => event k.val) =
      ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide (event k)) true).toReal := by
  rw [FiniteProbabilityWeights.eventProbability,
    shiftedSmoothProductFiniteWeights_mean_eq_tsum a S hS hZ
      (fun k => if event k then 1 else 0), pmf_map_toReal_indicator]
  apply tsum_congr
  intro k
  simp only [decide_eq_true_eq]

theorem shiftedSmoothPositiveGridWeights_point_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (k : shiftedSmoothPositiveGrid a S hS hZ) :
    (shiftedSmoothPositiveGridWeights a S hS hZ).weight k ≤
      (2 : ℝ) ^ Fintype.card I * (∏ i, S i)⁻¹ :=
  shiftedSmoothProductPMF_point_le a S hS hZ hlarge k.val

theorem shiftedSmoothScale_mesh_le_quarter {S : ℝ}
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) : 1 / S ≤ 1 / 4 := by
  have hp : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  exact (div_le_iff₀ (smoothSamplingScale_pos hlarge)).mpr (by linarith)

end Erdos3

end

end OAI
