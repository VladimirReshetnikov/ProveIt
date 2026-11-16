module
public import PA196.CheckCoverage
public import PA196.Coverage.S174
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
namespace PA196.Coverage.S176
theorem checked : CheckCoverage.blockCheck 2816 16 = true := by decide +kernel
end PA196.Coverage.S176
