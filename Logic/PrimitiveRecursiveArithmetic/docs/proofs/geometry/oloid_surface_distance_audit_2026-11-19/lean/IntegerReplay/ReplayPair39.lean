import ReplayBalls
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Oloid.Replay.Data
theorem P6_P10_direct : verifyTree b118 b328 32265348486011
  (.leaf [⟨-22723166579557,97384073136204,100000000000000⟩,⟨0,0,100000000000000⟩])
  [] = true := by decide +kernel

theorem P6_P10_upper : upperOK b118 [b328] [32265348486016] 32265348486020 = true := by decide +kernel
end Oloid.Replay.Data
