import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P7_P8_direct : verifyTree b131 b233 114520125294038
  (.leaf [⟨-19929384307621,-97993977575762,99999999999999⟩,⟨0,0,99999999999999⟩])
  [] = true := by decide +kernel

theorem P7_P8_upper : upperOK b131 [b233] [114520125294044] 114520125294048 = true := by decide +kernel
end Oloid.Replay.Data
