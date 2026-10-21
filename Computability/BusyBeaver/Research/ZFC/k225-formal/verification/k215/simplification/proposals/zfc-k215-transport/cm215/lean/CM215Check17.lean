import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check17 : chunk17.all stateCheck = true := by decide +kernel
 theorem oldCount17 : liveCount parentTable chunk17 = 0 := by decide +kernel
 theorem newCount17 : liveCount markerTable chunk17 = 0 := by decide +kernel
 theorem changed17 : changes chunk17 = 0 := by decide +kernel
end CM215Certificate
