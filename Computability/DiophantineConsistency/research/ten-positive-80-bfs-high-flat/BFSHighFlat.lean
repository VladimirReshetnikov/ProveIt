import BFSHighRunsV2

/-! Convert the generic high-digit expansion to the displayed interval sums. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSHighFlat
open Finset BFSHighRuns
open scoped BigOperators

theorem shift_sum (B start len : ℕ) :
    B^start * (∑ j ∈ range len, B^j) = ∑ j ∈ Ico start (start+len), B^j := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, pow_add, Finset.mul_sum]

theorem runs_high : runs CompactHighPopulation.mu CompactHighPopulation.padding
    CompactHighPopulation.lastPadding = CompactHighPopulation.highDigits := rfl

theorem expansion (B a b c : ℕ) : Nat.ofDigits B (runs a b c) =
    4 + (∑ j ∈ Ico 1013 1023, B^j) + (∑ j ∈ Ico 1065 1074, B^j) +
    B^2195 + B^3296 + a*(B^4393+B^5495) +
    b*(∑ j ∈ Ico 8792 8805, B^j) + c*B^8805 := by
  rw [BFSHighRuns.expansion]
  have h1 : B^1013 * (∑ j ∈ range 10, B^j) = ∑ j ∈ Ico 1013 1023, B^j := by
    simpa only [Nat.reduceAdd] using shift_sum B 1013 10
  have h2 : B^1065 * (∑ j ∈ range 9, B^j) = ∑ j ∈ Ico 1065 1074, B^j := by
    simpa only [Nat.reduceAdd] using shift_sum B 1065 9
  have h3 : B^8792 * (b * (∑ j ∈ range 13, B^j)) = b * (∑ j ∈ Ico 8792 8805, B^j) := by
    rw [mul_left_comm]
    simpa only [Nat.reduceAdd] using congrArg (fun x => b*x) (shift_sum B 8792 13)
  rw [h1, h2, h3]
  ring

#print axioms BFSHighFlat.expansion
end BFSHighFlat
