import PA194SourcePathDepth
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194PathDepthSharp

theorem at3248 : (PA194SourceProgram.path 3248).length = 36 := by decide +kernel
#print axioms at3248
end PA194PathDepthSharp
