import BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252
import BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252

/-!
Writing self-loop scans of the actual frozen252 arithmetic evaluator.
Read and written bits may differ. Scan length, state and both whole numeric
tape halves are internal IΣ1-model elements. The actual lookup row remains an
explicit premise. The endpoint includes every write and move, but does not
assert first exit, absolute head, a box effect or whole symbolic execution.

This supplies the all-internal counterpart of the attributed WritingRuns
contracts used by SymbolicPerm252. Mira-Cult, Jeff and Wade retain their
machine, verification and framework attributions.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance bitPrefix_delta (b : Bool) : 𝚫₁-Function₂[V] (bitPrefix b) :=
  (bitPrefix_defined b).graph_delta.to_definable
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom :=
  runFrom_defined_delta.to_definable
private instance frame_delta : 𝚫₁-Function₃[V] frame :=
  frame_defined.graph_delta.to_definable
private instance leftFrame_delta : 𝚫₁-Function₃[V] leftFrame := by
  unfold leftFrame
  definability

/-- One right step consumes a read bit and prepends the written bit to the
entire left half. The actual final move is part of the endpoint. -/
theorem step_right_run (read write : Bool) (state : V)
    (hrow : actionLookup state (digit read) = 4*state+3+digit write)
    (length left right : V) :
    stepValue (frame state left (bitPrefix read (length+1) right)) =
      frame state (2*left+digit write) (bitPrefix read length right) := by
  rw [bitPrefix_succ, step_right_row read write state state hrow]

/-- One left step consumes a read bit from the full left-facing half. -/
theorem step_left_run (read write : Bool) (state : V)
    (hrow : actionLookup state (digit read) = 4*state+1+digit write)
    (length left right : V) :
    stepValue (leftFrame state (bitPrefix read (length+1) left) right) =
      leftFrame state (bitPrefix read length left) (2*right+digit write) := by
  rw [bitPrefix_succ, step_left_recenter read write state state hrow]

def RightWritingScan (read write : Bool) (state length : V) : Prop := ∀ left right : V,
  runFrom length (frame state left (bitPrefix read length right)) =
    frame state (bitPrefix write length left) right
private instance rightWritingScan_definable (read write : Bool) (state : V) :
    𝚷₁-Predicate (RightWritingScan read write state) := by
  unfold RightWritingScan
  definability

def LeftWritingScan (read write : Bool) (state length : V) : Prop := ∀ left right : V,
  runFrom length (leftFrame state (bitPrefix read length left) right) =
    leftFrame state left (bitPrefix write length right)
private instance leftWritingScan_definable (read write : Bool) (state : V) :
    𝚷₁-Predicate (LeftWritingScan read write state) := by
  unfold LeftWritingScan
  definability

/-- Exactly length right moves with the same literal row; all consumed bits
are replaced and the entire remaining right half is retained. -/
theorem scan_right (read write : Bool) (state : V)
    (hrow : actionLookup state (digit read) = 4*state+3+digit write)
    (length left right : V) :
    runFrom length (frame state left (bitPrefix read length right)) =
      frame state (bitPrefix write length left) right := by
  have allLengths : ∀ length : V, RightWritingScan read write state length := by
    intro length
    induction length using ISigma1.pi1_succ_induction
    · exact rightWritingScan_definable read write state
    case zero => intro left right; simp
    case succ length ih =>
      intro left right
      rw [runFrom_first, step_right_run read write state hrow, ih, bitPrefix_push]
  exact allLengths length left right

/-- Exactly length left moves with possible replacement of every consumed bit.
The Π1 induction quantifies both whole halves, so its right parameter may change. -/
theorem scan_left (read write : Bool) (state : V)
    (hrow : actionLookup state (digit read) = 4*state+1+digit write)
    (length left right : V) :
    runFrom length (leftFrame state (bitPrefix read length left) right) =
      leftFrame state left (bitPrefix write length right) := by
  have allLengths : ∀ length : V, LeftWritingScan read write state length := by
    intro length
    induction length using ISigma1.pi1_succ_induction
    · exact leftWritingScan_definable read write state
    case zero => intro left right; simp
    case succ length ih =>
      intro left right
      rw [runFrom_first, step_left_run read write state hrow, ih, bitPrefix_push]
  exact allLengths length left right

/-- A fixed actual right-loop row lifts to every arithmetic model and internal
length. The supplied premise is finite lookup data, not an operation oracle. -/
theorem scan_right_numeral (read write : Bool) (state : Nat)
    (hrow : lookupNat literalRows 0 state read.toNat = 4*state+3+write.toNat)
    (length left right : V) :
    runFrom length (frame (state : V) left (bitPrefix read length right)) =
      frame (state : V) (bitPrefix write length left) right :=
  scan_right read write (state : V)
    (right_transition_of_nat read write state state hrow) length left right

/-- Fixed actual left-loop data, retaining its final write and move. -/
theorem scan_left_numeral (read write : Bool) (state : Nat)
    (hrow : lookupNat literalRows 0 state read.toNat = 4*state+1+write.toNat)
    (length left right : V) :
    runFrom length (leftFrame (state : V) (bitPrefix read length left) right) =
      leftFrame (state : V) left (bitPrefix write length right) :=
  scan_left read write (state : V)
    (left_transition_of_nat read write state state hrow) length left right

end SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252
