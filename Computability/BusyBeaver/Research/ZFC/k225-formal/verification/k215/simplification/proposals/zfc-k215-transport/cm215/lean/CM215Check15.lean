import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check15 : chunk15.all stateCheck = true := by decide +kernel
 theorem oldCount15 : liveCount parentTable chunk15 = 0 := by decide +kernel
 theorem newCount15 : liveCount markerTable chunk15 = 0 := by decide +kernel
 theorem changed15 : changes chunk15 = 0 := by decide +kernel
end CM215Certificate
