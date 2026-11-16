module
public import M6.Legacy211.SourceChecks
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Legacy211.Source.Checks048
theorem checked : M6.Legacy211.Source.blockCheck 3072 64=true := by decide +kernel
end M6.Legacy211.Source.Checks048
