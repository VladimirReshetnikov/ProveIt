/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.PhysicalBoundaryBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerIntervalBox_card_real {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i ≤ hi i) :
    ((Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))).card : ℝ) =
      ∏ i, ((hi i - lo i : ℤ) : ℝ) := by
  rw [Fintype.card_piFinset, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact_mod_cast Int.card_Ico_of_le (lo i) (hi i) (hlen i)

theorem integerIntervalBox_window_factor_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    (S : I → ℝ) (hS : ∀ i, 0 ≤ S i) {K : ℝ}
    (hside : ∀ i, S i ≤ K * ((hi i - lo i : ℤ) : ℝ)) :
    (3 : ℝ) ^ Fintype.card I * (∏ i, S i) /
      (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))).card ≤
        (3 * K) ^ Fintype.card I := by
  rw [integerIntervalBox_card_real lo hi (fun i => (hlen i).le)]
  have hlenR (i : I) : (0 : ℝ) < ((hi i - lo i : ℤ) : ℝ) := by
    exact_mod_cast sub_pos.mpr (hlen i)
  calc
    _ = ∏ i, 3 * (S i / ((hi i - lo i : ℤ) : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_div_distrib]
      ring
    _ ≤ ∏ _i : I, 3 * K := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (by norm_num) (div_nonneg (hS i) (hlenR i).le))
      (fun i _ => mul_le_mul_of_nonneg_left ((div_le_iff₀ (hlenR i)).mpr (hside i)) (by norm_num))
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

theorem translated_box_window_factor_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (S : I → ℝ) (hS : ∀ i, 0 ≤ S i) {K : ℝ}
    (hside : ∀ i, S i ≤ K * (N i : ℝ)) :
    (3 : ℝ) ^ Fintype.card I * (∏ i, S i) / (translatedIntegerBox lo N).card ≤
      (3 * K) ^ Fintype.card I := by
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod]
  have hNR (i : I) : (0 : ℝ) < N i := by exact_mod_cast hN i
  calc
    _ = ∏ i, 3 * (S i / (N i : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_div_distrib]
      ring
    _ ≤ ∏ _i : I, 3 * K := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (by norm_num) (div_nonneg (hS i) (hNR i).le))
      (fun i _ => mul_le_mul_of_nonneg_left ((div_le_iff₀ (hNR i)).mpr (hside i)) (by norm_num))
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
