module
public import PA196.Startup.S014
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0180 : run Literal.machine 128 c0180 = some c0181 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0181 : run Literal.machine 128 c0181 = some c0182 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0182 : run Literal.machine 128 c0182 = some c0183 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0183 : run Literal.machine 128 c0183 = some c0184 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0184 : run Literal.machine 128 c0184 = some c0185 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0185 : run Literal.machine 128 c0185 = some c0186 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0186 : run Literal.machine 128 c0186 = some c0187 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0187 : run Literal.machine 128 c0187 = some c0188 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0188 : run Literal.machine 128 c0188 = some c0189 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0189 : run Literal.machine 128 c0189 = some c0190 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0190 : run Literal.machine 128 c0190 = some c0191 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
theorem run0191 : run Literal.machine 128 c0191 = some c0192 := by
  exact FastRun.checked (by decide +kernel) (by decide +kernel)
end PA196.Startup
