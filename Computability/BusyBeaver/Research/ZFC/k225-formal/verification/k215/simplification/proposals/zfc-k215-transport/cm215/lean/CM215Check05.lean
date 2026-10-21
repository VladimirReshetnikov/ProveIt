import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check05 : chunk05.all stateCheck = true := by decide +kernel
 theorem oldCount05 : liveCount parentTable chunk05 = 16 := by decide +kernel
 theorem newCount05 : liveCount markerTable chunk05 = 16 := by decide +kernel
 theorem changed05 : changes chunk05 = 0 := by decide +kernel
end CM215Certificate
