import OAI.Combinatorics.Progressions.Nilpotent.SquarefreeBracketCoefficients

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem exponent_total_eq_zero_iff (a : ι →₀ ℕ) :
    (∑ i, a i) = 0 ↔ a = 0 := by
  classical
  constructor
  · intro h
    ext i
    have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hi
    exact Nat.eq_zero_of_le_zero hi
  · rintro rfl
    simp only [Finsupp.zero_apply, Finset.sum_const_zero]

theorem squarefreeExponent_total_le (a : SquarefreeIndex ι) :
    (∑ i, a.val i) ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ => a.property i
    _ = _ := by simp

theorem squarefreeDisjointAdd_total (a b : SquarefreeIndex ι)
    (hab : Disjoint a.val.support b.val.support) :
    (∑ i, (a.disjointAdd b hab).val i) = (∑ i, a.val i) + ∑ i, b.val i := by
  change (∑ i, (a.val + b.val) i) = _
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

end Erdos3

end

end OAI
