module
public import PA196.Startup.S001
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0024 : run Literal.machine 128 c0024 = some c0025 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0025 : run Literal.machine 128 c0025 = some c0026 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0026 : run Literal.machine 128 c0026 = some c0027 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0027 : run Literal.machine 128 c0027 = some c0028 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0028 : run Literal.machine 128 c0028 = some c0029 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0029 : run Literal.machine 128 c0029 = some c0030 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0030 : run Literal.machine 128 c0030 = some c0031 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0031 : run Literal.machine 128 c0031 = some c0032 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0032 : run Literal.machine 128 c0032 = some c0033 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0033 : run Literal.machine 128 c0033 = some c0034 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0034 : run Literal.machine 128 c0034 = some c0035 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0035 : run Literal.machine 128 c0035 = some c0036 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
