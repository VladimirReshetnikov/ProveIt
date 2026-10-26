import DiophantineConsistency.NativePreliminaryCount2011

namespace DiophantineConsistency.NativePreliminaryCount2011Checks

open NativePreliminaryCount2011

set_option Elab.async false

-- Both ends of the difficult phase range have the stated safe bound after
-- the padding staircase, while the easy small-phase endpoint needs no padding.
example : 2 * 942 + 57 + 1 + 2 ^ 6 = 2006 ∧
    2 * 462 + 57 + 1 + 2 ^ 10 = 2006 ∧ 2006 < 2048 := by decide

-- A raw phase10 clause can pass the ENTIRE mask with512 selectors unless
-- the padding information is used. This asserts no actual source solution.
example : (2 * 512 + 2 ^ 10 + 2048 * (2 ^ 34 - 1)) &&& (2 ^ 45 - 4) = 0 ∧
    (512 : ℕ) > 1 := by decide +kernel

-- Phase11 is already divisible by the whole low-clause modulus; so is
-- the final actual Boolean phase46.
example : (2 ^ 11 : ℕ) % 2048 = 0 ∧ (2 ^ 46 : ℕ) % 2048 = 0 := by decide

#print axioms clause_low_mask
#print axioms count_small_phase
#print axioms count_large_phase
#print axioms total_le_one_all_phases

end DiophantineConsistency.NativePreliminaryCount2011Checks
