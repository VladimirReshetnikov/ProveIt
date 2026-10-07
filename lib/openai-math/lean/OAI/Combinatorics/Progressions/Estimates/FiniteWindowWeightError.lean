/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_window_weight_error {V : Type*}
    (s t : Finset V) (a b φ : V → ℂ) (ε C : ℝ)
    (ha : ∀ v ∈ s, ‖a v‖ ≤ C) (hb : ∀ v ∈ t, ‖b v‖ ≤ C)
    (he : ∀ v ∈ s, v ∈ t → ‖a v - b v‖ ≤ ε) :
    ‖(∑ v ∈ s, a v * φ v) - ∑ v ∈ t, b v * φ v‖ ≤
      ∑ v ∈ s ∪ t, (if v ∈ s ∩ t then ε else C) * ‖φ v‖ := by
  have hs : (∑ v ∈ s, a v * φ v) =
      ∑ v ∈ s ∪ t, (if v ∈ s then a v else 0) * φ v := by
    calc
      _ = ∑ v ∈ s, (if v ∈ s then a v else 0) * φ v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [ite_eq_left hv]
      _ = _ := Finset.sum_subset Finset.subset_union_left (by
        intro v _ hv
        simp only [ite_eq_right hv, zero_mul])
  have ht : (∑ v ∈ t, b v * φ v) =
      ∑ v ∈ s ∪ t, (if v ∈ t then b v else 0) * φ v := by
    calc
      _ = ∑ v ∈ t, (if v ∈ t then b v else 0) * φ v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [ite_eq_left hv]
      _ = _ := Finset.sum_subset Finset.subset_union_right (by
        intro v _ hv
        simp only [ite_eq_right hv, zero_mul])
  rw [hs, ht, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v hv
  rw [← sub_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  by_cases hvs : v ∈ s
  · by_cases hvt : v ∈ t
    · simpa only [ite_eq_left hvs, ite_eq_left hvt, ite_eq_left (Finset.mem_inter.mpr ⟨hvs, hvt⟩)] using he v hvs hvt
    · have hnot : v ∉ s ∩ t := fun h => hvt (Finset.mem_inter.mp h).2
      simpa only [ite_eq_left hvs, ite_eq_right hvt, ite_eq_right hnot, sub_zero] using ha v hvs
  · have hvt : v ∈ t := (Finset.mem_union.mp hv).resolve_left hvs
    have hnot : v ∉ s ∩ t := fun h => hvs (Finset.mem_inter.mp h).1
    simpa only [ite_eq_right hvs, ite_eq_left hvt, ite_eq_right hnot, zero_sub, norm_neg] using hb v hvt

namespace FiniteProbabilityWeights

theorem norm_window_weight_error {Ω V : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (s t : Ω → Finset V)
    (a b φ : Ω → V → ℂ) (ε C : ℝ) {Z : ℝ} (hZ : 0 < Z)
    (ha : ∀ y, p.weight y ≠ 0 → ∀ v ∈ s y, ‖a y v‖ ≤ C)
    (hb : ∀ y, p.weight y ≠ 0 → ∀ v ∈ t y, ‖b y v‖ ≤ C)
    (he : ∀ y, p.weight y ≠ 0 → ∀ v ∈ s y, v ∈ t y → ‖a y v - b y v‖ ≤ ε) :
    ‖p.complexMean (fun y => ∑ v ∈ s y, a y v * φ y v) / (Z : ℂ) -
      p.complexMean (fun y => ∑ v ∈ t y, b y v * φ y v) / (Z : ℂ)‖ ≤
      p.mean (fun y => ∑ v ∈ s y ∪ t y,
        (if v ∈ s y ∩ t y then ε else C) * ‖φ y v‖) / Z := by
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply div_le_div_of_nonneg_right _ hZ.le
  exact p.norm_complexMean_sub_le _ _ _ (fun y hy =>
    finite_window_weight_error (s y) (t y) (a y) (b y) (φ y) ε C (ha y hy) (hb y hy) (he y hy))

end FiniteProbabilityWeights
end Erdos3

end

end OAI
