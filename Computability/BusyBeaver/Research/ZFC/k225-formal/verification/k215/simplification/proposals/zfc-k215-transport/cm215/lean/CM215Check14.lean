import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check14 : chunk14.all stateCheck = true := by decide +kernel
 theorem oldCount14 : liveCount parentTable chunk14 = 1 := by decide +kernel
 theorem newCount14 : liveCount markerTable chunk14 = 1 := by decide +kernel
 theorem changed14 : changes chunk14 = 0 := by decide +kernel
end CM215Certificate
