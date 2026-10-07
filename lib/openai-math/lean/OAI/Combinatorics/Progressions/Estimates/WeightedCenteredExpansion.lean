import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem weighted_product_count_of_centered {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (F : I → X → ℂ) (W : X → ℂ) {error : ℝ} (herror : 0 ≤ error)
    (hcentered : ∀ U ⊆ S, U.Nonempty →
      ‖𝔼 x, W x * (∏ i ∈ U, (F i x - 1))‖ ≤ error) :
    ‖(𝔼 x, W x * (∏ i ∈ S, F i x)) - (𝔼 x, W x)‖ ≤ (2 : ℝ) ^ S.card * error := by
  have hp (x : X) : (∏ i ∈ S, F i x) =
      ∑ U ∈ S.powerset, ∏ i ∈ U, (F i x - 1) := by
    simpa only [sub_add_cancel] using (Finset.prod_add_one (f := fun i => F i x - 1) S)
  have he : (𝔼 x, W x * (∏ i ∈ S, F i x)) - (𝔼 x, W x) =
      ∑ U ∈ S.powerset.erase ∅, 𝔼 x, W x * (∏ i ∈ U, (F i x - 1)) := by
    simp only [hp, Finset.mul_sum, Finset.expect_sum_comm]
    rw [← Finset.sum_erase_add _ _ (show ∅ ∈ S.powerset by simp)]
    simp
  rw [he]
  calc
    _ ≤ ∑ U ∈ S.powerset.erase ∅, ‖𝔼 x, W x * (∏ i ∈ U, (F i x - 1))‖ := norm_sum_le _ _
    _ ≤ ∑ _U ∈ S.powerset.erase ∅, error := by
      apply Finset.sum_le_sum
      intro U hU
      exact hcentered U (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hU))
        (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hU))
    _ = ((S.powerset.erase ∅).card : ℝ) * error := by simp
    _ ≤ (S.powerset.card : ℝ) * error := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (Finset.erase_subset ∅ S.powerset)) herror
    _ = _ := by simp

theorem norm_expect_finite_weighted_sum_le {J X : Type*} [Fintype J] [Fintype X]
    (c : J → ℂ) (H : J → X → ℂ) (f : X → ℂ) {error : ℝ}
    (h : ∀ j, ‖𝔼 x, H j x * f x‖ ≤ error) :
    ‖𝔼 x, (∑ j, c j * H j x) * f x‖ ≤ (∑ j, ‖c j‖) * error := by
  have he : (𝔼 x, (∑ j, c j * H j x) * f x) = ∑ j, c j * (𝔼 x, H j x * f x) := by
    simp only [Finset.sum_mul, Finset.expect_sum_comm, mul_assoc, ← Finset.mul_expect]
  rw [he]
  calc
    _ ≤ ∑ j, ‖c j * (𝔼 x, H j x * f x)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * error := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (h j) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

end Erdos3

end

end OAI
