module
public import PA196.Startup.S008
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0108 : run Literal.machine 128 c0108 = some c0109 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0109 : run Literal.machine 128 c0109 = some c0110 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0110 : run Literal.machine 128 c0110 = some c0111 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0111 : run Literal.machine 128 c0111 = some c0112 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0112 : run Literal.machine 128 c0112 = some c0113 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0113 : run Literal.machine 128 c0113 = some c0114 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0114 : run Literal.machine 128 c0114 = some c0115 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0115 : run Literal.machine 128 c0115 = some c0116 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0116 : run Literal.machine 128 c0116 = some c0117 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0117 : run Literal.machine 128 c0117 = some c0118 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0118 : run Literal.machine 128 c0118 = some c0119 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0119 : run Literal.machine 128 c0119 = some c0120 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
