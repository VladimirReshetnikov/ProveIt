module
public import M6PA.Model.OriginalCheck
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.Arithmetic.OriginalCoverage.S038
theorem checked : OriginalCheck.blockCheck 2432 64 = true := by decide +kernel
end M6.Arithmetic.OriginalCoverage.S038
