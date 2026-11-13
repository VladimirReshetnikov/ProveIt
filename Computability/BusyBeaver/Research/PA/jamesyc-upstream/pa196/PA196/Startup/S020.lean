module
public import PA196.Startup.S019
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0240 : run Literal.machine 128 c0240 = some c0241 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0241 : run Literal.machine 128 c0241 = some c0242 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0242 : run Literal.machine 128 c0242 = some c0243 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0243 : run Literal.machine 128 c0243 = some c0244 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0244 : run Literal.machine 128 c0244 = some c0245 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0245 : run Literal.machine 128 c0245 = some c0246 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0246 : run Literal.machine 128 c0246 = some c0247 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0247 : run Literal.machine 128 c0247 = some c0248 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0248 : run Literal.machine 128 c0248 = some c0249 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0249 : run Literal.machine 128 c0249 = some c0250 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0250 : run Literal.machine 128 c0250 = some c0251 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0251 : run Literal.machine 128 c0251 = some c0252 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
