import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check18 : chunk18.all stateCheck = true := by decide +kernel
 theorem oldCount18 : liveCount parentTable chunk18 = 2 := by decide +kernel
 theorem newCount18 : liveCount markerTable chunk18 = 2 := by decide +kernel
 theorem changed18 : changes chunk18 = 0 := by decide +kernel
end CM215Certificate
