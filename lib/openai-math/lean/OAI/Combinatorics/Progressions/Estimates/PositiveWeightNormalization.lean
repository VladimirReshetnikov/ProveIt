import OAI.Combinatorics.Progressions.Probability.NormalizedExpectationWeights

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem sum_pos_of_expect_pos {X : Type*} [Fintype X] (w : X → ℝ)
    (h : 0 < 𝔼 x, w x) : 0 < ∑ x, w x := by
  by_contra! hs
  have hz := div_nonpos_of_nonpos_of_nonneg hs (Nat.cast_nonneg (Fintype.card X) : (0 : ℝ) ≤ _)
  rw [← Fintype.expect_eq_sum_div_card] at hz
  exact (not_lt_of_ge hz) h

theorem ofPositiveWeights_div {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) {Z : ℝ} (hZ : 0 < Z) :
    ofPositiveWeights (fun x => w x / Z) (fun x => div_nonneg (hw x) hZ.le)
      (by rw [← Finset.sum_div]; exact div_pos hmass hZ) = ofPositiveWeights w hw hmass := by
  apply eq_of_weight_eq
  intro x
  change (w x / Z) / (∑ y, w y / Z) = w x / ∑ y, w y
  rw [← Finset.sum_div]
  field_simp [hZ.ne', hmass.ne']

theorem ofDensity_eq_ofPositiveWeights {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) (hmass : 0 < ∑ x, w x) :
    ofDensity w hw htotal = ofPositiveWeights w hw hmass := by
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    intro hc
    rw [Fintype.expect_eq_sum_div_card, hc, div_zero] at htotal
    norm_num at htotal
  have hs : (∑ x, w x) = (Fintype.card X : ℝ) := by
    rw [Fintype.expect_eq_sum_div_card] at htotal
    simpa only [one_mul] using (div_eq_iff hcard).mp htotal
  apply eq_of_weight_eq
  intro x
  change (Fintype.card X : ℝ)⁻¹ * w x = w x / ∑ y, w y
  rw [hs]
  ring

theorem ofDensity_div_eq_ofPositiveWeights {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) {Z : ℝ} (hZ : 0 < Z)
    (htotal : (𝔼 x, w x / Z) = 1) :
    ofDensity (fun x => w x / Z) (fun x => div_nonneg (hw x) hZ.le) htotal =
      ofPositiveWeights w hw hmass := by
  exact (ofDensity_eq_ofPositiveWeights (fun x => w x / Z)
    (fun x => div_nonneg (hw x) hZ.le) htotal
    (by rw [← Finset.sum_div]; exact div_pos hmass hZ)).trans (ofPositiveWeights_div w hw hmass hZ)

end Erdos3.FiniteProbabilityWeights

end

end OAI
