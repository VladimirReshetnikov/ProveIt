import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check03 : chunk03.all stateCheck = true := by decide +kernel
 theorem oldCount03 : liveCount parentTable chunk03 = 16 := by decide +kernel
 theorem newCount03 : liveCount markerTable chunk03 = 16 := by decide +kernel
 theorem changed03 : changes chunk03 = 1 := by decide +kernel
end CM215Certificate
