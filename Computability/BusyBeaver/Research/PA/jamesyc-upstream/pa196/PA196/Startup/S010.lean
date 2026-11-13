module
public import PA196.Startup.S009
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0120 : run Literal.machine 128 c0120 = some c0121 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0121 : run Literal.machine 128 c0121 = some c0122 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0122 : run Literal.machine 128 c0122 = some c0123 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0123 : run Literal.machine 128 c0123 = some c0124 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0124 : run Literal.machine 128 c0124 = some c0125 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0125 : run Literal.machine 128 c0125 = some c0126 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0126 : run Literal.machine 128 c0126 = some c0127 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0127 : run Literal.machine 128 c0127 = some c0128 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0128 : run Literal.machine 128 c0128 = some c0129 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0129 : run Literal.machine 128 c0129 = some c0130 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0130 : run Literal.machine 128 c0130 = some c0131 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0131 : run Literal.machine 128 c0131 = some c0132 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
