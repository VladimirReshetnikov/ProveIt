import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check00 : chunk00.all stateCheck = true := by decide +kernel
 theorem oldCount00 : liveCount parentTable chunk00 = 16 := by decide +kernel
 theorem newCount00 : liveCount markerTable chunk00 = 16 := by decide +kernel
 theorem changed00 : changes chunk00 = 0 := by decide +kernel
end CM215Certificate
