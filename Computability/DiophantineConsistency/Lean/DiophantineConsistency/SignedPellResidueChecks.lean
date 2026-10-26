import DiophantineConsistency.SignedPellResidue

namespace DiophantineConsistency.SignedPellResidueChecks

open SignedPellResidue

-- The odd recurrence has the required initial residue before sign selection.
example : Diophantine.yr 2 3 = 15 := by decide
example : Diophantine.yr 2 5 = 209 := by decide

-- Both the signed ordinate and the first-root quotient may be negative.
example : (4 * 2 ^ 2 : ℤ) ∣ (-15 : ℤ) - 1 := by
  exact four_square_dvd_sub_one (S := 2) (V := -13) (y := -15)
    (by norm_num) (by norm_num) (by norm_num [Int.ModEq])

-- A higher positive odd-index solution uses the same unbounded theorem.
example : (4 * 2 ^ 2 : ℤ) ∣ (209 : ℤ) - 1 := by
  exact four_square_dvd_sub_one (S := 2) (V := 181) (y := 209)
    (by norm_num) (by norm_num) (by norm_num [Int.ModEq])

-- The residue-modulo-four premise cannot simply be dropped.
example : (2 : ℤ) ^ 2 * 13 ^ 2 - (2 ^ 2 - 1) * 15 ^ 2 = 1 ∧
    ¬ (4 * 2 ^ 2 : ℤ) ∣ 15 - 1 := by norm_num

#print axioms odd_ordinate_modEq
#print axioms odd_index_of_base_dvd
#print axioms signed_residue_cases
#print axioms four_square_dvd_sub_one

end DiophantineConsistency.SignedPellResidueChecks
