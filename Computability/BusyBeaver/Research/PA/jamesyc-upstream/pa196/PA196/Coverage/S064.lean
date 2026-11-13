module
public import PA196.CheckCoverage
public import PA196.Coverage.S062
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace PA196.Coverage.S064
theorem checked : CheckCoverage.blockCheck 1024 16 = true := by decide +kernel
end PA196.Coverage.S064
