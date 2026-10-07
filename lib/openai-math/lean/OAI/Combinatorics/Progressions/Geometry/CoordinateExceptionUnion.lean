import OAI.Combinatorics.Progressions.Probability.ConditionalCoordinateExceptions

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_coordinate_exception_union {I G : Type*} [Fintype I] [DecidableEq I]
    [AddGroup G] [Fintype G] [DecidableEq G]
    (E : I → (I → G) → Finset G) {delta : ℝ}
    (hE : ∀ i t, ((E i t).card : ℝ) ≤ delta * Fintype.card G)
    (hindependent : ∀ i t a, E i (Function.update t i a) = E i t) :
    ∃ S : Finset (I → G),
      (S.card : ℝ) ≤ (Fintype.card I : ℝ) * delta * Fintype.card (I → G) ∧
      ∀ t, t ∉ S → ∀ i, -(t i) ∉ E i t := by
  classical
  let S : Finset (I → G) := Finset.univ.filter (fun t => ∃ i, -(t i) ∈ E i t)
  have hmean := finite_union_indicator_mean_le (fun i t => -(t i) ∈ E i t)
    (fun i => conditional_neg_coordinate_bad_mean i (E i) (hE i) (hindependent i))
  have hid : (𝔼 t : I → G, if ∃ i, -(t i) ∈ E i t then (1 : ℝ) else 0) =
      (S.card : ℝ) / Fintype.card (I → G) := by
    simp [Fintype.expect_eq_sum_div_card, S]
  rw [hid] at hmean
  refine ⟨S, ?_, ?_⟩
  · exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card (I → G))).mp hmean
  · intro t ht i hi
    exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, hi⟩⟩)

end Erdos3

end

end OAI
