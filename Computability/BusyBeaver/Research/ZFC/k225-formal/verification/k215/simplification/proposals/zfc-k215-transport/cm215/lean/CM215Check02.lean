import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check02 : chunk02.all stateCheck = true := by decide +kernel
 theorem oldCount02 : liveCount parentTable chunk02 = 16 := by decide +kernel
 theorem newCount02 : liveCount markerTable chunk02 = 16 := by decide +kernel
 theorem changed02 : changes chunk02 = 0 := by decide +kernel
end CM215Certificate
