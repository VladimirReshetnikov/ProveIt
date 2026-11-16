module
public import PA196.Startup.S033
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0408 : run Literal.machine 128 c0408 = some c0409 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0409 : run Literal.machine 128 c0409 = some c0410 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0410 : run Literal.machine 128 c0410 = some c0411 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0411 : run Literal.machine 128 c0411 = some c0412 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0412 : run Literal.machine 128 c0412 = some c0413 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0413 : run Literal.machine 128 c0413 = some c0414 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0414 : run Literal.machine 128 c0414 = some c0415 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0415 : run Literal.machine 128 c0415 = some c0416 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0416 : run Literal.machine 128 c0416 = some c0417 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0417 : run Literal.machine 128 c0417 = some c0418 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0418 : run Literal.machine 128 c0418 = some c0419 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0419 : run Literal.machine 128 c0419 = some c0420 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
