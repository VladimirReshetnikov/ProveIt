import DiophantineConsistency.MultiTargetCarry

open DiophantineConsistency.MultiTargetCarry
open Jones1982 Finset

private def positions : Finset ℕ := {1, 3}
private def h (i : ℕ) : ℤ := if i = 0 then 1 else if i = 2 then -2 else 0
private def bad (i : ℕ) : ℤ := if i = 1 then 1 else if i = 3 then -1 else 0

private theorem positions_bound : ∀ i ∈ positions, i < 4 := by
  intro i hi
  simp only [positions, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl <;> decide

private theorem h_bound : ∀ i < 4, |h i| < 2 ^ (3 - 1) := by
  intro i hi
  interval_cases i <;> norm_num [h]

private theorem bad_bound : ∀ i < 4, |bad i| < 2 ^ (3 - 1) := by
  intro i hi
  interval_cases i <;> norm_num [bad]

example : shiftedValue 3 4 h = 2213 := by decide
example : selectedMask 3 4 positions = 1560 := by decide
example : 2 * selectedMask 3 4 positions = (2 ^ 3 - 2) * (8 ^ 1 + 8 ^ 3) := by decide

example : τ 2 (2 * shiftedValue 3 4 h) (2 * selectedMask 3 4 positions) = 0 := by
  apply (tau_doubled_selected_iff (by decide) positions positions_bound h h_bound).mpr
  intro i hi
  simp only [positions, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl <;> decide

/-- An unweighted row sum can cancel; the mask still rejects both nonzero cells. -/
example : (∑ i ∈ positions, bad i) = 0 := by decide
example : τ 2 (2 * shiftedValue 3 4 bad) (2 * selectedMask 3 4 positions) ≠ 0 := by
  intro hz
  have hc := (tau_doubled_selected_iff (by decide) positions positions_bound bad bad_bound).mp hz
    1 (by decide)
  norm_num [bad] at hc

/-- Divisibility is derived symbolically, without evaluating the enormous binomial. -/
example : (2 ^ 13) ^ 2 ∣ (2 * centralRank 3 4 13 positions h).choose
    (centralRank 3 4 13 positions h) := by
  apply (central_divisibility_iff (by decide) positions positions_bound h h_bound
    (by decide) (by decide)).mpr
  intro i hi
  simp only [positions, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl <;> decide

#print axioms tau_shifted_selected_iff
#print axioms central_divisibility_iff
#print axioms central_quadratics_iff

#print axioms rowProduct_degree_lt
#print axioms doubled_shifted_rowProduct_cast
