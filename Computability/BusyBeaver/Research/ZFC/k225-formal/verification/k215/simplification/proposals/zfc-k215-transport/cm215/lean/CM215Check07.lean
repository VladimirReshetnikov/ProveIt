import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check07 : chunk07.all stateCheck = true := by decide +kernel
 theorem oldCount07 : liveCount parentTable chunk07 = 14 := by decide +kernel
 theorem newCount07 : liveCount markerTable chunk07 = 14 := by decide +kernel
 theorem changed07 : changes chunk07 = 0 := by decide +kernel
end CM215Certificate
