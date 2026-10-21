import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check12 : chunk12.all stateCheck = true := by decide +kernel
 theorem oldCount12 : liveCount parentTable chunk12 = 14 := by decide +kernel
 theorem newCount12 : liveCount markerTable chunk12 = 14 := by decide +kernel
 theorem changed12 : changes chunk12 = 1 := by decide +kernel
end CM215Certificate
