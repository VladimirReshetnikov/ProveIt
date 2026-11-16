module
public import PA196.Startup.S036
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0444 : run Literal.machine 128 c0444 = some c0445 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0445 : run Literal.machine 128 c0445 = some c0446 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0446 : run Literal.machine 128 c0446 = some c0447 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0447 : run Literal.machine 128 c0447 = some c0448 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0448 : run Literal.machine 128 c0448 = some c0449 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0449 : run Literal.machine 128 c0449 = some c0450 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0450 : run Literal.machine 128 c0450 = some c0451 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0451 : run Literal.machine 128 c0451 = some c0452 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0452 : run Literal.machine 128 c0452 = some c0453 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0453 : run Literal.machine 128 c0453 = some c0454 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0454 : run Literal.machine 42 c0454 = some c0455 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
