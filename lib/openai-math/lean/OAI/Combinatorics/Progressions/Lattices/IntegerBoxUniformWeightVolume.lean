import OAI.Combinatorics.Progressions.Geometry.BoxPairDivisibility

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem integerBox_volume_pos (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) :
    0 < ∏ i, ((hi i - lo i : ℤ) : ℝ) := by
  apply Finset.prod_pos
  intro i _
  exact_mod_cast sub_pos.mpr (hlen i)

theorem integerBoxUniformWeights_weight_eq_inv_volume
    [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    (y : ∀ i, Finset.Ico (lo i) (hi i)) :
    (integerBoxUniformWeights lo hi hlen).weight y =
      (∏ i, ((hi i - lo i : ℤ) : ℝ))⁻¹ := by
  change (∏ i, (Fintype.card (Finset.Ico (lo i) (hi i)) : ℝ)⁻¹) = _
  rw [Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_coe, Int.card_Ico]
  exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hlen i).le)

end Erdos3

end

end OAI
