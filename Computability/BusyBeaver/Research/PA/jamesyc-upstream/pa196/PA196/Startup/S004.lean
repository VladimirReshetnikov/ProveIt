module
public import PA196.Startup.S003
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0048 : run Literal.machine 128 c0048 = some c0049 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0049 : run Literal.machine 128 c0049 = some c0050 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0050 : run Literal.machine 128 c0050 = some c0051 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0051 : run Literal.machine 128 c0051 = some c0052 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0052 : run Literal.machine 128 c0052 = some c0053 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0053 : run Literal.machine 128 c0053 = some c0054 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0054 : run Literal.machine 128 c0054 = some c0055 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0055 : run Literal.machine 128 c0055 = some c0056 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0056 : run Literal.machine 128 c0056 = some c0057 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0057 : run Literal.machine 128 c0057 = some c0058 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0058 : run Literal.machine 128 c0058 = some c0059 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0059 : run Literal.machine 128 c0059 = some c0060 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
