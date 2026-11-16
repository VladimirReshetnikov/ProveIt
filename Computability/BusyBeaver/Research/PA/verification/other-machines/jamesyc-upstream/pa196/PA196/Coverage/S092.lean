module
public import PA196.CheckCoverage
public import PA196.Coverage.S090
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace PA196.Coverage.S092
theorem checked : CheckCoverage.blockCheck 1472 16 = true := by decide +kernel
end PA196.Coverage.S092
