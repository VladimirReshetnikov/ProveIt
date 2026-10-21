import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check13 : chunk13.all stateCheck = true := by decide +kernel
 theorem oldCount13 : liveCount parentTable chunk13 = 14 := by decide +kernel
 theorem newCount13 : liveCount markerTable chunk13 = 14 := by decide +kernel
 theorem changed13 : changes chunk13 = 0 := by decide +kernel
end CM215Certificate
