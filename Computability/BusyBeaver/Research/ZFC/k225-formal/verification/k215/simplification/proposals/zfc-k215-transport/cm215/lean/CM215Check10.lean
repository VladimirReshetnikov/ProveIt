import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check10 : chunk10.all stateCheck = true := by decide +kernel
 theorem oldCount10 : liveCount parentTable chunk10 = 15 := by decide +kernel
 theorem newCount10 : liveCount markerTable chunk10 = 15 := by decide +kernel
 theorem changed10 : changes chunk10 = 1 := by decide +kernel
end CM215Certificate
