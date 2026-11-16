import PA194AX11HSource
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PA194AX11HPrepRows
open M6.Source

def oldPrep : List Instruction := [
  .dec 4 (some 3591) (some 3588),
  .inc 1 (some 3589),
  .inc 6 (some 3590),
  .jump (some 3587),
  .dec 6 (some 3594) (some 3592),
  .inc 4 (some 3593),
  .jump (some 3591),
  .dec 2 (some 3602) (some 3595),
  .inc 7 (some 3596),
  .dec 6 (some 3598) (some 3597),
  .jump (some 3601),
  .dec 7 (some 3601) (some 3599),
  .inc 6 (some 3600),
  .jump (some 3598),
  .jump (some 3594),
  .dec 7 (some 3605) (some 3603),
  .inc 2 (some 3604),
  .jump (some 3602),
  .dec 1 (some 3609) (some 3606),
  .inc 7 (some 3607),
  .inc 6 (some 3608),
  .jump (some 3605),
  .dec 6 (some 3615) (some 3610),
  .inc 7 (some 3611),
  .dec 6 (some 3614) (some 3612),
  .inc 1 (some 3613),
  .jump (some 3611),
  .jump (some 3605),
  .dec 7 (some 3621) (some 3616),
  .inc 1 (some 3617),
  .inc 1 (some 3618),
  .inc 1 (some 3619),
  .inc 1 (some 3620),
  .jump (some 3615),
  .dec 1 (some 3624) (some 3622),
  .inc 6 (some 3623),
  .jump (some 3621)
]

def newPrep : List Instruction := [
  .dec 4 (some 3609) (some 3606),
  .inc 1 (some 3607),
  .inc 6 (some 3608),
  .jump (some 3605),
  .dec 6 (some 3612) (some 3610),
  .inc 4 (some 3611),
  .jump (some 3609),
  .dec 2 (some 3620) (some 3613),
  .inc 7 (some 3614),
  .dec 6 (some 3616) (some 3615),
  .jump (some 3619),
  .dec 7 (some 3619) (some 3617),
  .inc 6 (some 3618),
  .jump (some 3616),
  .jump (some 3612),
  .dec 7 (some 3623) (some 3621),
  .inc 2 (some 3622),
  .jump (some 3620),
  .dec 1 (some 3627) (some 3624),
  .inc 7 (some 3625),
  .inc 6 (some 3626),
  .jump (some 3623),
  .dec 6 (some 3633) (some 3628),
  .inc 7 (some 3629),
  .dec 6 (some 3632) (some 3630),
  .inc 1 (some 3631),
  .jump (some 3629),
  .jump (some 3623),
  .dec 7 (some 3639) (some 3634),
  .inc 1 (some 3635),
  .inc 1 (some 3636),
  .inc 1 (some 3637),
  .inc 1 (some 3638),
  .jump (some 3633),
  .dec 1 (some 3642) (some 3640),
  .inc 6 (some 3641),
  .jump (some 3639)
]

def relocate : Instruction → Instruction
  | .inc r next => .inc r (next.map (· + 18))
  | .dec r zero positive => .dec r (zero.map (· + 18)) (positive.map (· + 18))
  | .jump next => .jump (next.map (· + 18))
  | .halt => .halt

theorem exact_prep : oldPrep.map relocate = newPrep := by decide +kernel
#print axioms exact_prep
end PA194AX11HPrepRows
