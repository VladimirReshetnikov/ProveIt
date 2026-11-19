import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P3_P4_direct : verifyTree b2 b36 117353638366591
  (.leaf [⟨-23706751374533,-97149317749873,99999999999999⟩,⟨0,0,99999999999999⟩])
  [] = true := by decide +kernel

theorem P3_P4_upper : upperOK b2 [b36] [117353638366598] 117353638366602 = true := by decide +kernel
end Oloid.Replay.Data
