module
public import M6.Legacy213.SourceCheck
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Legacy213.SourceCheckShards.S026
theorem checked : M6.Legacy213.SourceCheck.rangeCheck 1664 64 = true := by decide +kernel
end M6.Legacy213.SourceCheckShards.S026
