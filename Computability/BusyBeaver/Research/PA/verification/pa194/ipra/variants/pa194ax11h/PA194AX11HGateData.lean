import PA194AX11HGateRows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194AX11HGateData
open M6.Source PA194AX11HGateRows

def gateData : List Instruction := [
  .dec 3 (some 3523) (some 3520),
  .inc 7 (some 3521),
  .inc 6 (some 3522),
  .jump (some 3519),
  .dec 5 (some 3527) (some 3524),
  .dec 6 (some 3526) (some 3525),
  .jump (some 3523),
  .jump (some 3528),
  .dec 6 (some 3533) (some 3528),
  .dec 5 (some 3530) (some 3529),
  .jump (some 3528),
  .dec 6 (some 3532) (some 3531),
  .jump (some 3528),
  .jump (some 3535),
  .dec 1 (some 3535) (some 3534),
  .jump (some 3533),
  .dec 7 (some 3538) (some 3536),
  .inc 6 (some 3537),
  .jump (some 3535),
  .dec 4 (some 3541) (some 3539),
  .inc 5 (some 3540),
  .jump (some 3538),
  .dec 5 (some 3545) (some 3542),
  .dec 6 (some 3544) (some 3543),
  .jump (some 3541),
  .jump (some 3546),
  .dec 6 (some 3551) (some 3546),
  .dec 5 (some 3548) (some 3547),
  .jump (some 3546),
  .dec 6 (some 3550) (some 3549),
  .jump (some 3546),
  .jump (some 3553),
  .dec 1 (some 3553) (some 3552),
  .jump (some 3551)
]

theorem data_correct : newGate = gateData.map some := by decide +kernel
#print axioms data_correct
end PA194AX11HGateData
