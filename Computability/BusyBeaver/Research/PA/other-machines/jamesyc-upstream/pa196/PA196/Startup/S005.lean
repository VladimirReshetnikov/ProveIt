module
public import PA196.Startup.S004
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0060 : run Literal.machine 128 c0060 = some c0061 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0061 : run Literal.machine 128 c0061 = some c0062 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0062 : run Literal.machine 128 c0062 = some c0063 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0063 : run Literal.machine 128 c0063 = some c0064 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0064 : run Literal.machine 128 c0064 = some c0065 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0065 : run Literal.machine 128 c0065 = some c0066 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0066 : run Literal.machine 128 c0066 = some c0067 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0067 : run Literal.machine 128 c0067 = some c0068 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0068 : run Literal.machine 128 c0068 = some c0069 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0069 : run Literal.machine 128 c0069 = some c0070 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0070 : run Literal.machine 128 c0070 = some c0071 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0071 : run Literal.machine 128 c0071 = some c0072 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
