import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem card_filter_le_cutoff_of_injective
    {L : Type*} [Fintype L] (p : L → ℕ) (hp : Function.Injective p)
    (cutoff : ℕ) :
    (Finset.univ.filter (fun l => p l ≤ cutoff)).card ≤ cutoff + 1 := by
  classical
  have hcard := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun l => p l ≤ cutoff))
    (t := Finset.range (cutoff + 1)) p
    (fun l hl => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_filter.mp hl).2))
    (fun _ _ _ _ heq => hp heq)
  simpa only [Finset.card_range] using hcard

theorem prod_filter_le_cutoff_pow_of_injective
    {L : Type*} [Fintype L] (p : L → ℕ) (hp : Function.Injective p)
    (cutoff : ℕ) :
    (∏ l ∈ Finset.univ.filter (fun l => p l ≤ cutoff), p l) ≤
      (cutoff + 1) ^ (cutoff + 1) := by
  classical
  calc
    _ ≤ (cutoff + 1) ^ (Finset.univ.filter (fun l => p l ≤ cutoff)).card :=
      Finset.prod_le_pow_card _ p (cutoff + 1)
        (fun l hl => (Finset.mem_filter.mp hl).2.trans (Nat.le_succ cutoff))
    _ ≤ _ := Nat.pow_le_pow_right (Nat.succ_pos cutoff)
      (card_filter_le_cutoff_of_injective p hp cutoff)

end Erdos3

end

end OAI
