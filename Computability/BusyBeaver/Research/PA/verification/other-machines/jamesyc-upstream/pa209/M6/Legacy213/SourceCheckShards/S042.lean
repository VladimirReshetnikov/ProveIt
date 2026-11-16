module
public import M6.Legacy213.FastSourceCheck
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Legacy213.SourceCheckShards.S042
theorem checked : M6.Legacy213.FastSourceCheck.check 2688 64 = true := by decide +kernel
end M6.Legacy213.SourceCheckShards.S042
