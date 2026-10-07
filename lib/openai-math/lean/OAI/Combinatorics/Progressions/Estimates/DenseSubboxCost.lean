import OAI.Combinatorics.Progressions.Geometry.SampledCommonBox
import OAI.Combinatorics.Progressions.Probability.ProductSliceAxisDensity

namespace OAI

section

namespace Erdos3

theorem IsDenseCommonStrideBox.of_large_subbox {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A B : Finset (I → ℤ)} (hB : IsDenseCommonStrideBox N p B)
    (hshape : ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
      0 < m ∧ (∀ i, 0 < H i) ∧ A = commonStrideBox c m H)
    (hsub : A ⊆ B) (hloss : 2 * (1 - (A.card : ℝ) / B.card) ≤ 1) :
    IsDenseCommonStrideBox N (p + 1) A := by
  obtain ⟨c, m, H, hm, hH, hBsub, hBdense, rfl⟩ := hB
  obtain ⟨c', m', H', hm', hH', rfl⟩ := hshape
  have haxis (i : I) : (integerProgressionSupport (c i) m (H i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hm] using hH i)
  have haxis' (i : I) : (integerProgressionSupport (c' i) m' (H' i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hm'] using hH' i)
  refine ⟨c', m', H', hm', hH', ?_, ?_, rfl⟩
  · intro i
    exact (piFinset_axis_subset _ _ haxis' hsub i).trans (hBsub i)
  · intro i
    have hi := piFinset_card_ratio_le_axis _ _ haxis' haxis hsub i
    simp only [card_integerProgressionSupport _ _ _ hm, card_integerProgressionSupport _ _ _ hm'] at hi
    have hhalf : (1 / 2 : ℝ) ≤ (H' i : ℝ) / H i := by
      change ((commonStrideBox c' m' H').card : ℝ) / (commonStrideBox c m H).card ≤ _ at hi
      linarith
    have hlen : (H i : ℝ) ≤ 2 * H' i := by
      have ht := (le_div_iff₀ (by exact_mod_cast hH i : (0 : ℝ) < H i)).mp hhalf
      linarith
    have he : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
      simpa only [show -(p + 1) = -p - 1 by ring] using exp_sub_one_le_half_exp (-p)
    have hmul := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (N i))
    nlinarith [hBdense i]

end Erdos3

end

end OAI
