import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P1_P9_direct : verifyTree b0 b327 132216021712579
  (.leaf [⟨16751143449806,98587013308670,100000000000000⟩,⟨0,0,100000000000000⟩])
  [] = true := by decide +kernel

theorem P1_P9_upper : upperOK b0 [b327] [132216021712585] 132216021712589 = true := by decide +kernel
end Oloid.Replay.Data
