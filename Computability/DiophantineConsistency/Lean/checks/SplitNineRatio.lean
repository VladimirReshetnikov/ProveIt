import DiophantineConsistency.SplitNineRatio

open DiophantineConsistency.SplitNineRatio

-- Rank positivity is independent of the source words, including zero words.
example (S T : ℕ) : 8 ≤ rank 0 1 S T := (size_bounds 0 S T (by decide)).1

-- The zero-base boundary explains why the numerical contract assumes b>0.
example : rank 0 0 0 0 = 0 := by
  norm_num [rank, blockLength, base, DiophantineConsistency.NativeBaseBounds52.base,
    DiophantineConsistency.ReducedRankCarry.rank]

-- The sharper compact tuple uses an even radix exponent. No parity premise
-- is needed for the exact population calibration or outer numerical ratio.
example (k : ℕ) :
    threshold 864014 (2 ^ k) = 2 ^ (6912197 + k + 1201 * (864026 + 2 * k)) := by
  simpa only [show 8 * (864014 + 12) - 11 = 6912197 by decide,
    show 864014 + 12 = 864026 by decide] using
    (threshold_power (a := 864014) (b := 2 ^ k) rfl)

#print axioms base_bounds
#print axioms size_bounds
#print axioms base_power
#print axioms blockLength_power
#print axioms threshold_power
#print axioms rank_cast
#print axioms binomial_iff
#print axioms sound
#print axioms complete
