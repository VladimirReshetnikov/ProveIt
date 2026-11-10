import DiophantineConsistency.Sign17KControlAppend
import DiophantineConsistency.Sign17KControlBlocks

/-! SOURCE-ONLY: assemble symbolic control blocks into the actual control sum. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KControlBlockSum
open Sign17KControlBlocks
open scoped BigOperators

theorem symbolic_sum (r : ℕ) :
    (∑ i : Fin 44, symbolic i * r ^ (1005 - (942 + i.val))) =
      Sign17KRankedRawWord.controls r := by
  unfold symbolic
  rw [Sign17KControlAppend.append_power_sum south
    (Fin.append gap9 (Fin.append north (Fin.append east (Fin.append gap1 west)))) r 942]
  rw [Sign17KControlAppend.append_power_sum gap9
    (Fin.append north (Fin.append east (Fin.append gap1 west))) r 951]
  rw [Sign17KControlAppend.append_power_sum north
    (Fin.append east (Fin.append gap1 west)) r 960]
  rw [Sign17KControlAppend.append_power_sum east (Fin.append gap1 west) r 969]
  rw [Sign17KControlAppend.append_power_sum gap1 west r 977]
  simp only [south, gap9, north, east, gap1, west, Nat.reduceAdd, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, Sign17KRankedRawWord.controls]
  omega

theorem literal_sum_eq (r : ℕ) :
    (∑ i : Fin 44, literal i * r ^ (1005 - (942 + i.val))) =
      ∑ i : Fin 44, symbolic i * r ^ (1005 - (942 + i.val)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [symbolic_eq_literal]

theorem controls_as_sum (r : ℕ) :
    Sign17KRankedRawWord.controls r =
      ∑ i : Fin 44, literal i * r ^ (1005 - (942 + i.val)) := by
  rw [literal_sum_eq, symbolic_sum]

end DiophantineConsistency.Sign17KControlBlockSum
#print axioms DiophantineConsistency.Sign17KControlBlockSum.symbolic_sum
#print axioms DiophantineConsistency.Sign17KControlBlockSum.literal_sum_eq
#print axioms DiophantineConsistency.Sign17KControlBlockSum.controls_as_sum
