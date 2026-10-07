import OAI.Combinatorics.Progressions.Estimates.FiniteSectionPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteSectionCount_le (n : ℕ) (s : Fin n → Bool) : finiteSectionCount s ≤ n := by
  rw [finiteSectionCount_eq_card]
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin n => s i = true)

theorem finiteSectionCount_eq_zero_iff (n : ℕ) (s : Fin n → Bool) :
    finiteSectionCount s = 0 ↔ ∀ i, s i = false := by
  constructor
  · intro h i
    apply Bool.eq_false_iff.mpr
    intro hi
    have hb : (if s i then 1 else 0) ≤ finiteSectionCount s :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (if s j then 1 else 0)) (Finset.mem_univ i)
    simp only [hi, ite_true, h] at hb
    omega
  · intro h
    simp only [finiteSectionCount, h, Bool.false_eq_true, ite_false, Finset.sum_const_zero]

end Erdos3

end

end OAI
