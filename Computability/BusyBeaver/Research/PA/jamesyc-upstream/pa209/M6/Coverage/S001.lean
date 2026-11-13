module
public import M6.CheckCoverage
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.Coverage.S001
theorem checked : CheckCoverage.blockCheck 64 64 = true := by decide +kernel
end M6.Coverage.S001
