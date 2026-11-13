module
public import M6PA.Model.OriginalCheck
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.Arithmetic.OriginalCoverage.S031
theorem checked : OriginalCheck.blockCheck 1984 64 = true := by decide +kernel
end M6.Arithmetic.OriginalCoverage.S031
