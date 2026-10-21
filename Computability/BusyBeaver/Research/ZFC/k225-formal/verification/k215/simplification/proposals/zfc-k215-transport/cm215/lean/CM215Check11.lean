import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check11 : chunk11.all stateCheck = true := by decide +kernel
 theorem oldCount11 : liveCount parentTable chunk11 = 14 := by decide +kernel
 theorem newCount11 : liveCount markerTable chunk11 = 14 := by decide +kernel
 theorem changed11 : changes chunk11 = 2 := by decide +kernel
end CM215Certificate
