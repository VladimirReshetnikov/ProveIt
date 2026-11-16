module
public import PA196.Startup.S024
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0300 : run Literal.machine 128 c0300 = some c0301 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0301 : run Literal.machine 128 c0301 = some c0302 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0302 : run Literal.machine 128 c0302 = some c0303 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0303 : run Literal.machine 128 c0303 = some c0304 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0304 : run Literal.machine 128 c0304 = some c0305 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0305 : run Literal.machine 128 c0305 = some c0306 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0306 : run Literal.machine 128 c0306 = some c0307 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0307 : run Literal.machine 128 c0307 = some c0308 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0308 : run Literal.machine 128 c0308 = some c0309 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0309 : run Literal.machine 128 c0309 = some c0310 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0310 : run Literal.machine 128 c0310 = some c0311 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0311 : run Literal.machine 128 c0311 = some c0312 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
