module
public import M6.SourceCrosswalkBase
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.SourceCrosswalk.S033
theorem checked : blockCheck 2112 64 = true := by decide +kernel
end M6.SourceCrosswalk.S033
