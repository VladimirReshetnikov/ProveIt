module
public import PA196.Startup.S010
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0132 : run Literal.machine 128 c0132 = some c0133 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0133 : run Literal.machine 128 c0133 = some c0134 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0134 : run Literal.machine 128 c0134 = some c0135 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0135 : run Literal.machine 128 c0135 = some c0136 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0136 : run Literal.machine 128 c0136 = some c0137 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0137 : run Literal.machine 128 c0137 = some c0138 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0138 : run Literal.machine 128 c0138 = some c0139 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0139 : run Literal.machine 128 c0139 = some c0140 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0140 : run Literal.machine 128 c0140 = some c0141 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0141 : run Literal.machine 128 c0141 = some c0142 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0142 : run Literal.machine 128 c0142 = some c0143 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0143 : run Literal.machine 128 c0143 = some c0144 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
