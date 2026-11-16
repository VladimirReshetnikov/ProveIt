import PA194AX11HRelocation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PA194AX11HPushRows
open M6.Source

def oldPush : List Instruction := [
  .dec 1 (some 3571) (some 3569),
  .inc 6 (some 3570),
  .jump (some 3568),
  .dec 2 (some 3574) (some 3572),
  .inc 1 (some 3573),
  .jump (some 3571),
  .dec 1 (some 3578) (some 3575),
  .inc 7 (some 3576),
  .inc 6 (some 3577),
  .jump (some 3574),
  .dec 6 (some 3584) (some 3579),
  .inc 7 (some 3580),
  .dec 6 (some 3583) (some 3581),
  .inc 1 (some 3582),
  .jump (some 3580),
  .jump (some 3574),
  .dec 7 (some 3587) (some 3585),
  .inc 2 (some 3586),
  .jump (some 3584)
]

def newPush : List Instruction := [
  .dec 1 (some 3556) (some 3554),
  .inc 6 (some 3555),
  .jump (some 3553),
  .dec 2 (some 3559) (some 3557),
  .inc 1 (some 3558),
  .jump (some 3556),
  .dec 1 (some 3563) (some 3560),
  .inc 7 (some 3561),
  .inc 6 (some 3562),
  .jump (some 3559),
  .dec 6 (some 3569) (some 3564),
  .inc 7 (some 3565),
  .dec 6 (some 3568) (some 3566),
  .inc 1 (some 3567),
  .jump (some 3565),
  .jump (some 3559),
  .dec 7 (some 3572) (some 3570),
  .inc 2 (some 3571),
  .jump (some 3569)
]

def relocate : Instruction → Instruction
  | .inc r next => .inc r (next.map (· + 15))
  | .dec r zero positive => .dec r (zero.map (· + 15)) (positive.map (· + 15))
  | .jump next => .jump (next.map (· + 15))
  | .halt => .halt

/-- All 19 revised literal source instructions match the primary push,
    with their branch and exit destinations shifted by 15. -/
theorem exact_push : newPush.map relocate = oldPush := by decide +kernel
#print axioms exact_push
end PA194AX11HPushRows
