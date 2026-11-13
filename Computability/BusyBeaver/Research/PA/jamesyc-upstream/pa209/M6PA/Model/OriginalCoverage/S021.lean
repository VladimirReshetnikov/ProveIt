module
public import M6PA.Model.OriginalCheck
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.Arithmetic.OriginalCoverage.S021
theorem checked : OriginalCheck.blockCheck 1344 64 = true := by decide +kernel
end M6.Arithmetic.OriginalCoverage.S021
