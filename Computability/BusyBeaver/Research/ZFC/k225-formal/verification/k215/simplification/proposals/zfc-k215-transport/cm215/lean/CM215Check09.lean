import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check09 : chunk09.all stateCheck = true := by decide +kernel
 theorem oldCount09 : liveCount parentTable chunk09 = 16 := by decide +kernel
 theorem newCount09 : liveCount markerTable chunk09 = 16 := by decide +kernel
 theorem changed09 : changes chunk09 = 1 := by decide +kernel
end CM215Certificate
