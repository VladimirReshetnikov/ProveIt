import OAI.Combinatorics.Progressions.Estimates.FreimanInverseLift
import OAI.Combinatorics.Progressions.Estimates.SmallDifferenceGrowth

namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclic_model (A : Finset ℤ) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (hsmall : ((A - A).card : ℝ) ≤ K * A.card)
    (s : ℕ) (hs : 0 < s) :
    ∃ (N : ℕ) (A' : Finset ℤ) (B : Finset (ZMod N)) (f : ℤ → ZMod N),
      0 < N ∧ A'.Nonempty ∧ A' ⊆ A ∧ A.card ≤ (2 * s) * A'.card ∧
      B.Nonempty ∧ B = A'.image f ∧ B.card = A'.card ∧
      IsAddFreimanIso s (A' : Set ℤ) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card ∧
      (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  let D := s • A - s • A
  have hD : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate s a).sum ∈ s • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate s a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hN : 0 < 2 * D.card := Nat.mul_pos (by decide) hD.card_pos
  obtain ⟨A', B, f, hA'ne, hA'sub, hsize, hB, hf⟩ :=
    exists_large_cyclic_freiman_model A s hA hs
  have hBcard : B.card = A'.card := by
    rw [hB]
    exact Finset.card_image_of_injOn hf.bijOn.injOn
  have hBne : B.Nonempty := Finset.card_pos.mp (hBcard ▸ hA'ne.card_pos)
  have hDsize : (D.card : ℝ) ≤ K ^ (2 * s) * A.card := by
    simpa only [D, two_mul] using Erdos3.higher_difference_card_le A hA hsmall s s
  have hNsize : ((2 * D.card : ℕ) : ℝ) ≤ 2 * K ^ (2 * s) * A.card := by
    push_cast
    calc
      2 * (D.card : ℝ) ≤ 2 * (K ^ (2 * s) * A.card) :=
        mul_le_mul_of_nonneg_left hDsize (by norm_num)
      _ = _ := by ring
  have hsizeR : (A.card : ℝ) ≤ (2 * (s : ℝ)) * B.card := by
    rw [hBcard]
    exact_mod_cast hsize
  have hmodelSize : ((2 * D.card : ℕ) : ℝ) ≤
      (4 * (s : ℝ) * K ^ (2 * s)) * B.card := by
    calc
      ((2 * D.card : ℕ) : ℝ) ≤ 2 * K ^ (2 * s) * A.card := hNsize
      _ ≤ 2 * K ^ (2 * s) * ((2 * (s : ℝ)) * B.card) :=
        mul_le_mul_of_nonneg_left hsizeR (by positivity)
      _ = _ := by ring
  have hdensity : (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤
      (B.card : ℝ) / (2 * D.card : ℕ) := by
    apply (le_div_iff₀ (by exact_mod_cast hN)).mpr
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hmodelSize
  exact ⟨2 * D.card, A', B, f, hN, hA'ne, hA'sub, hsize, hBne, hB,
    hBcard, hf, hNsize, hdensity⟩

end Erdos3.FreimanModel

end

end OAI
