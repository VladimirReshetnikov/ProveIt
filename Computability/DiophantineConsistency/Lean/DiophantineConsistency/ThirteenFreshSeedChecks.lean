import DiophantineConsistency.ThirteenFreshSeed

/-! Focused checks of the fresh seed's sign, quotient and transport hypotheses. -/

open DiophantineConsistency.ThirteenFreshSeed

-- A nontrivial instance of both quotient congruences; the literal T is positive.
example : ∃ T : ℤ, 0 < T ∧ 8097 = 26 ^ 2 * (15 * T - 3) - 15 := by
  exact quotient_exists (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- The carrier allows a negative signed ordinate and a positive independent m.
example : ∃ m : ℤ, 0 < m ∧ -23 = 1 + 4 * (3 * (m - 13 ^ 2 * 6) - 6) := by
  exact carrier_exists (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- Rank 1 has the opposite Q sign; the construction needs rank 3 modulo 4.
example : Jones1980.Qh 0 (1 - (2 : ℤ) ^ 2) ≠ -Diophantine.yr 2 1 := by
  norm_num [Jones1980.Qh, Diophantine.yr]

-- G=0 cannot produce a positive m for this negative signed target.
example : ¬ ∃ m : ℤ, 0 < m ∧ -15 = 1 + 4 * (1 * (m - 13 ^ 2 * 0) - 0) := by
  norm_num
  omega

-- The exact normalized strong identity gives the factor required by value69.
example {delta b c f i : ℤ} (h : f ^ 2 - delta * (b * i * c ^ 2) ^ 2 = 1) :
    delta * f ^ 2 - (delta * (b * i * c ^ 2)) ^ 2 = delta := by
  linear_combination delta * h

#print axioms quotient_exists
#print axioms carrier_exists
#print axioms auxiliary_exists
#print axioms fresh_private_seed
