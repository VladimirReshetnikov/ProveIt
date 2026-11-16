import PA194AX11HSource
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PA194AX11HFieldRows
open M6.Source

def oldField : List Instruction := [
  .dec 8 (some 3562) (some 3555),
  .inc 7 (some 3556),
  .dec 6 (some 3558) (some 3557),
  .jump (some 3561),
  .dec 7 (some 3561) (some 3559),
  .inc 6 (some 3560),
  .jump (some 3558),
  .jump (some 3554),
  .dec 7 (some 3565) (some 3563),
  .inc 8 (some 3564),
  .jump (some 3562),
  .dec 6 (some 3568) (some 3566),
  .inc 4 (some 3567),
  .jump (some 3565)
]

def newField : List Instruction := [
  .dec 8 (some 3580) (some 3573),
  .inc 7 (some 3574),
  .dec 6 (some 3576) (some 3575),
  .jump (some 3579),
  .dec 7 (some 3579) (some 3577),
  .inc 6 (some 3578),
  .jump (some 3576),
  .jump (some 3572),
  .dec 7 (some 3583) (some 3581),
  .inc 8 (some 3582),
  .jump (some 3580),
  .dec 6 (some 3586) (some 3584),
  .inc 4 (some 3585),
  .jump (some 3583)
]

def relocate : Instruction → Instruction
  | .inc r next => .inc r (next.map (· + 18))
  | .dec r zero positive => .dec r (zero.map (· + 18)) (positive.map (· + 18))
  | .jump next => .jump (next.map (· + 18))
  | .halt => .halt

theorem exact_field : oldField.map relocate = newField := by decide +kernel
#print axioms exact_field
end PA194AX11HFieldRows
