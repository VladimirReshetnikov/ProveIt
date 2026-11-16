import PA194ORChecks

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194ORMovedFirst
open PA194ORChecks

theorem chunk224 : blockCheck 224 24 = true := by decide +kernel
theorem chunk248 : blockCheck 248 24 = true := by decide +kernel
theorem chunk272 : blockCheck 272 19 = true := by decide +kernel

theorem allMoved (i : Nat) (lower : 224 ≤ i) (upper : i ≤ 290) : checkAt i = true := by
  by_cases hi : i < 248
  · exact block_sound chunk224 lower (by omega)
  by_cases hi' : i < 272
  · exact block_sound chunk248 (by omega) (by omega)
  · exact block_sound chunk272 (by omega) (by omega)

#print axioms allMoved
end PA194ORMovedFirst
