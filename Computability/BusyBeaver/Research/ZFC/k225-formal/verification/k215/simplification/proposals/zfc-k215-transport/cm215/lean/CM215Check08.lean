import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check08 : chunk08.all stateCheck = true := by decide +kernel
 theorem oldCount08 : liveCount parentTable chunk08 = 15 := by decide +kernel
 theorem newCount08 : liveCount markerTable chunk08 = 15 := by decide +kernel
 theorem changed08 : changes chunk08 = 0 := by decide +kernel
end CM215Certificate
