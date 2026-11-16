import PA194ORChecks

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194ORMovedSecond
open PA194ORChecks

theorem chunk3554 : blockCheck 3554 24 = true := by decide +kernel
theorem chunk3578 : blockCheck 3578 24 = true := by decide +kernel
theorem chunk3602 : blockCheck 3602 19 = true := by decide +kernel

theorem allMoved (i : Nat) (lower : 3554 ≤ i) (upper : i ≤ 3620) : checkAt i = true := by
  by_cases hi : i < 3578
  · exact block_sound chunk3554 lower (by omega)
  by_cases hi' : i < 3602
  · exact block_sound chunk3578 (by omega) (by omega)
  · exact block_sound chunk3602 (by omega) (by omega)

#print axioms allMoved
end PA194ORMovedSecond
