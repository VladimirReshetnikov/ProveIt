import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.ListGetDCases

/-! Exact block and digit lookup facts for the current high-mask list. -/
namespace DiophantineConsistency.CurrentHighDigitFacts2011
open CurrentMasks2011

/-- The high-mask list as consecutive constant blocks. -/
theorem highDigits_blocks : highDigits =
    List.replicate 1 4 ++ List.replicate 916 8 ++ List.replicate 43 0 ++
      List.replicate 9 1 ++ List.replicate 18 0 ++ List.replicate 8 1 ++
      List.replicate 9 0 ++ List.replicate 1 1 ++
      List.replicate 1 (2^45-4) ++ List.replicate 1005 0 := by
  simp only [highDigits, highPrefix, List.replicate_one,
    List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 2000000 in
/-- The concrete digit at each position of the high-mask list. -/
theorem highDigits_getD (j : ℕ) : highDigits.getD j 0 =
    if j = 0 then 4 else if j < 917 then 8 else if j < 960 then 0 else
      if j < 969 then 1 else if j < 987 then 0 else if j < 995 then 1 else
      if j < 1004 then 0 else if j = 1004 then 1 else if j = 1005 then 2^45-4 else 0 := by
  rw [highDigits_blocks]
  simp only [List.append_assoc, ListGetDCases.append, List.length_replicate,
    ListGetDCases.replicate]
  repeat' first | omega | split


end DiophantineConsistency.CurrentHighDigitFacts2011
