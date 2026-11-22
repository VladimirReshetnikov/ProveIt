import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P2_P9_direct : verifyTree b1 b327 20848796288107
  (.leaf [⟨87761012021854,-47937508997648,99999999999998⟩,⟨0,0,99999999999998⟩])
  [] = true := by decide +kernel

theorem P2_P9_upper : upperOK b1 [b327] [20848796288112] 20848796288116 = true := by decide +kernel
end Oloid.Replay.Data
