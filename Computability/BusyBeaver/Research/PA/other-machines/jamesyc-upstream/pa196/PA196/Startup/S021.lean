module
public import PA196.Startup.S020
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0252 : run Literal.machine 128 c0252 = some c0253 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0253 : run Literal.machine 128 c0253 = some c0254 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0254 : run Literal.machine 128 c0254 = some c0255 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0255 : run Literal.machine 128 c0255 = some c0256 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0256 : run Literal.machine 128 c0256 = some c0257 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0257 : run Literal.machine 128 c0257 = some c0258 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0258 : run Literal.machine 128 c0258 = some c0259 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0259 : run Literal.machine 128 c0259 = some c0260 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0260 : run Literal.machine 128 c0260 = some c0261 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0261 : run Literal.machine 128 c0261 = some c0262 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0262 : run Literal.machine 128 c0262 = some c0263 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0263 : run Literal.machine 128 c0263 = some c0264 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
