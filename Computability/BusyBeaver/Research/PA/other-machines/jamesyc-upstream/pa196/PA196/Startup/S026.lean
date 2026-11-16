module
public import PA196.Startup.S025
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0312 : run Literal.machine 128 c0312 = some c0313 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0313 : run Literal.machine 128 c0313 = some c0314 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0314 : run Literal.machine 128 c0314 = some c0315 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0315 : run Literal.machine 128 c0315 = some c0316 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0316 : run Literal.machine 128 c0316 = some c0317 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0317 : run Literal.machine 128 c0317 = some c0318 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0318 : run Literal.machine 128 c0318 = some c0319 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0319 : run Literal.machine 128 c0319 = some c0320 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0320 : run Literal.machine 128 c0320 = some c0321 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0321 : run Literal.machine 128 c0321 = some c0322 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0322 : run Literal.machine 128 c0322 = some c0323 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0323 : run Literal.machine 128 c0323 = some c0324 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
