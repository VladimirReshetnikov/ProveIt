import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P5_P6_direct : verifyTree b88 b118 103605755069158
  (.leaf [⟨-85921987906326,51160648883931,99999999999999⟩,⟨0,0,99999999999999⟩])
  [] = true := by decide +kernel

theorem P5_P6_upper : upperOK b88 [b118] [103605755069165] 103605755069169 = true := by decide +kernel
end Oloid.Replay.Data
