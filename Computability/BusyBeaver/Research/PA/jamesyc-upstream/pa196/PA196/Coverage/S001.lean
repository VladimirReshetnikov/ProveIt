module
public import PA196.CheckCoverage
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace PA196.Coverage.S001
theorem checked : CheckCoverage.blockCheck 16 16 = true := by decide +kernel
end PA196.Coverage.S001
