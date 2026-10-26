import DiophantineConsistency.SidonPositions
import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination

namespace SidonMomentCheck
open DiophantineConsistency.SidonPositions

theorem weight_sum_eq_iff_short {m : ℕ} (i j k l : Fin (m + 1)) :
    weight m i + weight m j = weight m k + weight m l ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    obtain ⟨hsum, hsquares⟩ := sums_of_weight_sum_eq h
    simp only [Fin.ext_iff]
    zify at hsum hsquares ⊢
    have hfactor : 2 * (((i.val : ℤ) - k.val) * ((i.val : ℤ) - l.val)) = 0 := by
      linear_combination hsquares + ((i.val : ℤ) - j.val - k.val - l.val) * hsum
    have hz : ((i.val : ℤ) - k.val) * ((i.val : ℤ) - l.val) = 0 := by omega
    rcases mul_eq_zero.mp hz with h | h
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Nat.add_comm _ _

#print axioms weight_sum_eq_iff_short
end SidonMomentCheck
