import PA194AX11HSource
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace PA194AX11HSecondPushRows
open PA194AX11HSource PA194AX11HPushRows

/-- Relocate every target of an instruction by a fixed natural offset. -/
def shift (offset : Nat) : M6.Source.Instruction → M6.Source.Instruction
  | .inc r n => .inc r (n.map (· + offset))
  | .dec r z p => .dec r (z.map (· + offset)) (p.map (· + offset))
  | .jump n => .jump (n.map (· + offset))
  | .halt => .halt

/-- The second candidate push is the already-verified inserted push with
all program locations translated forward by 33. -/
theorem second_push_record (i : Fin 19) :
    PA194AX11HSource.program[3586+i.val]'(by rw [program_length]; have := i.isLt; omega) =
      some (shift 33 (newPush.getD i.val .halt)) := by
  fin_cases i <;> decide +kernel

#print axioms second_push_record
end PA194AX11HSecondPushRows
