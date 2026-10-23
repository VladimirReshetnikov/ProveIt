import DiophantineConsistency.NearSquareFinalizer

open DiophantineConsistency.NearSquareFinalizer

-- A concrete vanishing signed-root factor with a nonnegative ninth witness.
example : value 1 4 2 3 2 4 2 1 1 = 0 := by decide
example : value 1 4 2 3 2 4 2 1 11 = 0 := by decide

-- The new odd margin factor excludes the entire zero-margin branch.
example : ¬ ∃ n : ℕ, value 1 4 2 3 2 4 2 0 n = 0 := by
  rw [exists_value_zero_iff (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num

-- Neither a nonsquare radicand nor a failed divisibility can admit a zero.
example : ¬ ∃ n : ℕ, value 2 4 2 3 2 4 2 1 n = 0 := by
  intro h
  have ha := (exists_value_zero_iff (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mp h
  rcases ha.1 with ⟨r, hr⟩
  have : r ^ 2 = 2 := by nlinarith [hr]
  have hlo : -1 ≤ r := by nlinarith [sq_nonneg (r + 1)]
  have hhi : r ≤ 1 := by nlinarith [sq_nonneg (r - 1)]
  interval_cases r <;> norm_num at this

example : ¬ ∃ n : ℕ, value 1 4 2 3 2 3 2 1 n = 0 := by
  rw [exists_value_zero_iff (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num

-- Boundary-size arithmetic registers, independently evaluated.
example : (3 * (8 * (1 : ℤ) ^ 2 - 4 * 1 - 1)) ^ 2 - 64 * 1 * 1 = 17 := by decide
example : (3 * (8 * (9 : ℤ) ^ 2 - 4 * 9 - 1) * 2 * 1) ^ 2 -
    64 * 9 * 5833 * 4 = 324 := by decide
example : 0 < 3 * (8 * (9 : ℤ) ^ 2 - 4 * 9 - 1) * 2 * 1 ∧
    0 < (64 : ℤ) * 9 * 5833 * 4 ∧
    64 * 9 * 5833 * 4 < (3 * (8 * (9 : ℤ) ^ 2 - 4 * 9 - 1) * 2 * 1) ^ 2 := by
  exact full_majorant_bounds (t := 3) (D := 9) (F := 5833) (G := 2) (H := 1) (I := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

#print axioms rational_roots_of_norm_zero
#print axioms integer_roots_of_norm_zero
#print axioms full_majorant_bounds
#print axioms exists_value_zero_iff
