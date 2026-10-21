import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check06 : chunk06.all stateCheck = true := by decide +kernel
 theorem oldCount06 : liveCount parentTable chunk06 = 15 := by decide +kernel
 theorem newCount06 : liveCount markerTable chunk06 = 15 := by decide +kernel
 theorem changed06 : changes chunk06 = 0 := by decide +kernel
end CM215Certificate
