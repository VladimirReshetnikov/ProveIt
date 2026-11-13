module
public import PA196.Startup.S005
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0072 : run Literal.machine 128 c0072 = some c0073 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0073 : run Literal.machine 128 c0073 = some c0074 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0074 : run Literal.machine 128 c0074 = some c0075 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0075 : run Literal.machine 128 c0075 = some c0076 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0076 : run Literal.machine 128 c0076 = some c0077 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0077 : run Literal.machine 128 c0077 = some c0078 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0078 : run Literal.machine 128 c0078 = some c0079 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0079 : run Literal.machine 128 c0079 = some c0080 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0080 : run Literal.machine 128 c0080 = some c0081 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0081 : run Literal.machine 128 c0081 = some c0082 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0082 : run Literal.machine 128 c0082 = some c0083 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0083 : run Literal.machine 128 c0083 = some c0084 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
