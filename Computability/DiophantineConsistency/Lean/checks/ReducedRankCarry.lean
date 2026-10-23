import DiophantineConsistency.ReducedRankCarry

open Jones1982 DiophantineConsistency.ReducedRankCarry

example : (2 ^ 2) ^ 2 ∣ (2 * rank (2 ^ 3) 1 2).choose (rank (2 ^ 3) 1 2) :=
  (calibrated_iff (by decide) (by decide)).mpr ((τ_two_eq_zero_iff 1 2).mpr (by decide))

example : ¬ (2 ^ 2) ^ 2 ∣ (2 * rank (2 ^ 3) 1 1).choose (rank (2 ^ 3) 1 1) := by
  rw [calibrated_iff (by decide) (by decide), τ_two_eq_zero_iff]
  decide

-- Exponent zero of b is included in every calibrated instance.
example :
    (0 + 2279 * (864027 + 2 * 0)) + (139 * (864027 + 2 * 0) - 31 * 0 - 22) =
      2 * ((8 * 864027 - 11) + 0 + 1201 * (864027 + 2 * 0)) :=
  split116_calibration (by decide) 0

#print axioms rank
#print axioms rank_cast
#print axioms population
#print axioms calibrated_iff
#print axioms split116_calibrated_iff
