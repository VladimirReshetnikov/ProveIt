import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check01 : chunk01.all stateCheck = true := by decide +kernel
 theorem oldCount01 : liveCount parentTable chunk01 = 16 := by decide +kernel
 theorem newCount01 : liveCount markerTable chunk01 = 16 := by decide +kernel
 theorem changed01 : changes chunk01 = 0 := by decide +kernel
end CM215Certificate
