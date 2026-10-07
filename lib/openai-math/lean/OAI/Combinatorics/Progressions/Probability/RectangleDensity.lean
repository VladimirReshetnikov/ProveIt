import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

theorem rectangle_density_bounds {ι κ : Type*} {A S : Finset ι} {B T : Finset κ}
    (hAS : A ⊆ S) (hBT : B ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    {delta : ℝ} (hdelta : 0 < delta)
    (hprod : delta * (S.card : ℝ) * T.card ≤ (A.card : ℝ) * B.card) :
    A.Nonempty ∧ B.Nonempty ∧
      delta * (S.card : ℝ) ≤ A.card ∧ delta * (T.card : ℝ) ≤ B.card := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hAc : (0 : ℝ) ≤ A.card := by positivity
  have hBc : (0 : ℝ) ≤ B.card := by positivity
  have hASc : (A.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hAS
  have hBTc : (B.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hBT
  have hab : 0 < (A.card : ℝ) * B.card :=
    lt_of_lt_of_le (by positivity) hprod
  have ha : (0 : ℝ) < A.card := (mul_pos_iff.mp hab).resolve_right
    (fun h => (not_lt_of_ge hAc) h.1)
    |>.1
  have hb : (0 : ℝ) < B.card := (mul_pos_iff.mp hab).resolve_right
    (fun h => (not_lt_of_ge hAc) h.1)
    |>.2
  have hleft : delta * (S.card : ℝ) ≤ A.card := by
    apply (mul_le_mul_iff_left₀ hTc).mp
    nlinarith [mul_le_mul_of_nonneg_left hBTc hAc]
  have hright : delta * (T.card : ℝ) ≤ B.card := by
    apply (mul_le_mul_iff_left₀ hSc).mp
    nlinarith [mul_le_mul_of_nonneg_right hASc hBc]
  exact ⟨Finset.card_pos.mp (by exact_mod_cast ha),
    Finset.card_pos.mp (by exact_mod_cast hb), hleft, hright⟩

end Erdos3

end

end OAI
