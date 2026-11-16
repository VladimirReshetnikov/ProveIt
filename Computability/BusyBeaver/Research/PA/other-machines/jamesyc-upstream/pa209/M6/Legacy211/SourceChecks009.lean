module
public import M6.Legacy211.SourceChecks
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Legacy211.Source.Checks009
theorem checked : M6.Legacy211.Source.blockCheck 576 64=true := by decide +kernel
end M6.Legacy211.Source.Checks009
