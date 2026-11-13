module
public import PA196.Startup.S034
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0420 : run Literal.machine 128 c0420 = some c0421 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0421 : run Literal.machine 128 c0421 = some c0422 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0422 : run Literal.machine 128 c0422 = some c0423 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0423 : run Literal.machine 128 c0423 = some c0424 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0424 : run Literal.machine 128 c0424 = some c0425 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0425 : run Literal.machine 128 c0425 = some c0426 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0426 : run Literal.machine 128 c0426 = some c0427 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0427 : run Literal.machine 128 c0427 = some c0428 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0428 : run Literal.machine 128 c0428 = some c0429 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0429 : run Literal.machine 128 c0429 = some c0430 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0430 : run Literal.machine 128 c0430 = some c0431 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0431 : run Literal.machine 128 c0431 = some c0432 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
