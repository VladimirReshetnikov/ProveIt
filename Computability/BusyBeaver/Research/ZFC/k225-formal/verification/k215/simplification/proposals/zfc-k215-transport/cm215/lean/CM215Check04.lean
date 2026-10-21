import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check04 : chunk04.all stateCheck = true := by decide +kernel
 theorem oldCount04 : liveCount parentTable chunk04 = 15 := by decide +kernel
 theorem newCount04 : liveCount markerTable chunk04 = 15 := by decide +kernel
 theorem changed04 : changes chunk04 = 0 := by decide +kernel
end CM215Certificate
