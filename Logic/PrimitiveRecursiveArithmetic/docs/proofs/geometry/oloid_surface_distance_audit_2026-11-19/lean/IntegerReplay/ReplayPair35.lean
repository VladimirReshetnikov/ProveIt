import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P5_P10_direct : verifyTree b88 b328 128107537902724
  (.leaf [⟨-75211681374983,65902981607419,99999999999999⟩,⟨0,0,99999999999999⟩])
  [] = true := by decide +kernel

theorem P5_P10_upper : upperOK b88 [b328] [128107537902731] 128107537902735 = true := by decide +kernel
end Oloid.Replay.Data
