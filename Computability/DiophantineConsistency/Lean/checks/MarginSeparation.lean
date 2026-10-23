import DiophantineConsistency.MarginSeparation

open DiophantineConsistency.MarginSeparation

example : 2 * (1 : ℤ) ^ 2 * 1 < (1 * (1 + 1)) ^ 2 :=
  ratio_P_lt_A_sq (by decide)

example : 0 < 3 * (1 : ℤ) * 4 - 2 * (1 ^ 2 - 1) ∧
    3 * (1 : ℤ) * 4 - 2 * (1 ^ 2 - 1) < 3 * 4 ^ 2 :=
  Q_bounds (by decide) (by decide)

example : (12 : ℤ) < 3 * (8 * 49 ^ 2 - 4 * 49 - 1) * 2 * 1 :=
  Q_lt_second_majorant (C := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : (2 : ℤ) < 4 :=
  coordinate_gt_of_margin_pos (Y := 2) (cap := 100) (g := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : 0 < ((3 : ℤ) ^ 2 - 1) * 2 ^ 2 + 1 ∧
    0 < (3 : ℤ) * 2 ∧ ((3 : ℤ) ^ 2 - 1) * 2 ^ 2 + 1 < (3 * 2) ^ 2 :=
  first_majorant (by decide) (by decide)

example : ((3 : ℤ) ^ 2 - 1) * 2 ^ 2 + 1 < 49 * 4 * 4 :=
  radicand_lt_of_margin_pos (A := 2) (C := 4) (Y := 2) (cap := 100) (g := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms coordinate_gt_of_margin_pos
#print axioms radicand_lt_of_margin_pos
#print axioms pell_register_bounds
#print axioms Q_lt_second_majorant
