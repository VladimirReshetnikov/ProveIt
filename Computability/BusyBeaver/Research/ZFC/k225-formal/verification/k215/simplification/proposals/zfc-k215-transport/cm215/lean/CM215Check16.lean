import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check16 : chunk16.all stateCheck = true := by decide +kernel
 theorem oldCount16 : liveCount parentTable chunk16 = 0 := by decide +kernel
 theorem newCount16 : liveCount markerTable chunk16 = 0 := by decide +kernel
 theorem changed16 : changes chunk16 = 0 := by decide +kernel
end CM215Certificate
