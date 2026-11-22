import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P1_P2_direct : verifyTree b0 b1 140395034929643
  (.leaf [⟨2742675939935,99962381567709,99999999999999⟩,⟨0,0,99999999999999⟩])
  [] = true := by decide +kernel

theorem P1_P2_upper : upperOK b0 [b1] [140395034929650] 140395034929654 = true := by decide +kernel
end Oloid.Replay.Data
