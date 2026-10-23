import DiophantineConsistency.MarginFinalizer

open DiophantineConsistency.MarginFinalizer

-- All four signed root sums occur with the same literal arithmetic data.
example : value 1 1 2 9 2 4 1 0 = 0 := by decide
example : value 1 1 2 9 2 4 1 2 = 0 := by decide
example : value 1 1 2 9 2 4 1 16 = 0 := by decide
example : value 1 1 2 9 2 4 1 18 = 0 := by decide

-- Zero and negative margins are excluded before any radicand integrality.
example : ¬ ∃ n : ℕ, value 2 1 2 9 2 4 0 n = 0 := by
  rintro ⟨n, hn⟩
  have := margin_pos_of_value_zero (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hn
  omega

example : ¬ ∃ n : ℕ, value 2 1 2 9 2 4 (-1) n = 0 := by
  rintro ⟨n, hn⟩
  have := margin_pos_of_value_zero (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hn
  omega

-- The scalar norm cannot bypass the divisibility condition.
example : ¬ ∃ n : ℕ, value 1 1 2 9 2 3 1 n = 0 := by
  rw [exists_value_zero_iff (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by intro _; decide)]
  norm_num

-- A nonsquare first radicand is likewise rejected.
example : ¬ ∃ n : ℕ, value 2 1 2 9 2 4 1 n = 0 := by
  rintro ⟨n, hn⟩
  have h := conditions_of_value_zero (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro _; decide) hn
  obtain ⟨r, hr⟩ := h.1
  have hr' : r ^ 2 = 2 := by nlinarith [hr]
  have hlo : -1 ≤ r := by nlinarith [sq_nonneg (r + 1)]
  have hhi : r ≤ 1 := by nlinarith [sq_nonneg (r - 1)]
  interval_cases r <;> norm_num at hr'

-- Separation is essential: equal radicands permit a zero signed-root sum
-- without either radicand being a square. The generic theorem excludes
-- precisely this branch by its conditional hypothesis.
example : value 128 2 12 12 1 1 1 23 = 0 := by decide
example : ¬ (128 : ℤ) < 64 * 2 := by decide

#print axioms norm_pos_of_nonpositive_scale
#print axioms integer_roots_of_separated_norm_zero
#print axioms margin_pos_of_value_zero
#print axioms exists_value_zero_iff
