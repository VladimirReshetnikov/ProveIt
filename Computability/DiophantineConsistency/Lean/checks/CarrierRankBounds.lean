import DiophantineConsistency.CarrierRankBounds

open DiophantineConsistency.CarrierRankBounds

-- A transport unit at the smallest beta used by the uniform theorem.
example : (29 + 1 : ℤ) * (32 - 1 - 1) + (32 - 1) - 30 * (32 - 1) = 1 := by
  norm_num

example : (0 : ℤ) < 32 - 1 - 1 :=
  carrier_pos_of_transport (by norm_num) (by norm_num : (0 : ℤ) < 29)
    (by norm_num : (0 : ℤ) < 1) (by norm_num : (0 : ℤ) < 1)
    (by norm_num : (0 : ℤ) < 30) (by norm_num)

example : rank 32 1 1 32 1 1 = 985151 := by norm_num [rank]

example : 1 < rank 32 1 1 32 1 1 ∧ rank 32 1 1 32 1 1 + 2 < (1 : ℤ) * 1 * 32 ^ 4 :=
  rank_window (beta := 31) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms carrier_pos_of_transport
#print axioms rank_bounds
#print axioms rank_window
