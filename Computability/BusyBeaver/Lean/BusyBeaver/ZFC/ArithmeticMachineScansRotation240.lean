import BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252
import BusyBeaver.ZFC.ArithmeticMachineRunFromRotation240

set_option autoImplicit false

/-!
Internal single-row and writing-scan contracts for the exact Rotation240 table.
The generic tape prefix, frame and action-decoding algebra is reused from the
checked Perm252 development. Every execution below uses the Rotation240 lookup
and run. Lengths, states and both complete tape halves are internal IΣ1 values.
The row premises are exact lookup equations; numeral variants lift finite data.
These are endpoint contracts, not first-exit or complete register simulation.
The proof structure follows ArithmeticRegisterForwardPerm252,
ArithmeticRegisterReturnPerm252 and ArithmeticWritingScansPerm252. Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt retain their attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
open ArithmeticMachineGraphPerm252 (lookupNat)
open ArithmeticMachineStepPerm252 (genericStepValue)
open ArithmeticMachineUniformScansPerm252
open ArithmeticMachineGraphRotation240 ArithmeticMachineStepRotation240
open ArithmeticMachineRunFromRotation240

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance bitPrefix_delta (b : Bool) : 𝚫₁-Function₂[V] (bitPrefix b) :=
  (bitPrefix_defined b).graph_delta.to_definable
private instance frame_delta : 𝚫₁-Function₃[V] frame :=
  frame_defined.graph_delta.to_definable
private instance leftFrame_delta : 𝚫₁-Function₃[V] leftFrame := by
  unfold leftFrame
  definability
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom :=
  runFrom_defined_delta.to_definable

/-- A right-moving row retains its final write and move, including target zero. -/
theorem step_right_row (read write : Bool) (q target : V)
    (hrow : actionLookup q (digit read) = 4*target+3+digit write) (left suffix : V) :
    stepValue (frame q left (2*suffix+digit read)) =
      frame target (2*left+digit write) suffix := by
  have hn : 4*target+3+digit (V := V) write ≠ 0 := by
    rw [show (4*target+3+digit write : V) = (4*target+2+digit write)+1 by ring]
    simp
  unfold frame
  change genericStepValue actionLookup (cantor q (cantor left (2*suffix+digit read))) = _
  simp only [genericStepValue, first_cantor, second_cantor, digit_mod_two, hrow, if_neg hn]
  rw [apply_right, digit_div_two]
  rfl

/-- The analogous left row keeps both tape halves and the written cell. -/
theorem step_left_row (read write : Bool) (q target : V)
    (hrow : actionLookup q (digit read) = 4*target+1+digit write) (left suffix : V) :
    stepValue (frame q left (2*suffix+digit read)) =
      leftFrame target left (2*suffix+digit write) := by
  have hn : 4*target+1+digit (V := V) write ≠ 0 := by
    rw [show (4*target+1+digit write : V) = (4*target+digit write)+1 by ring]
    simp
  unfold frame
  change genericStepValue actionLookup (cantor q (cantor left (2*suffix+digit read))) = _
  simp only [genericStepValue, first_cantor, second_cantor, digit_mod_two, hrow, if_neg hn]
  rw [apply_left, digit_div_two]
  unfold leftFrame
  congr 2
  ring

theorem step_left_recenter (read write : Bool) (q target : V)
    (hrow : actionLookup q (digit read) = 4*target+1+digit write) (left right : V) :
    stepValue (leftFrame q (2*left+digit read) right) =
      leftFrame target left (2*right+digit write) := by
  have he : leftFrame q (2*left+digit read) right =
      frame q left (2*right+digit read) := by
    unfold leftFrame
    rw [digit_div_two, digit_mod_two]
    congr 1
    ring
  rw [he, step_left_row read write q target hrow]

theorem right_transition_of_nat (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+3+write.toNat) :
    actionLookup (q : V) (digit read) = 4*(target : V)+3+digit write := by
  have h := actionLookup_numeral (V := V) q read.toNat
  rw [hrow] at h
  cases read <;> cases write <;> simpa [digit, numeral_eq_natCast] using h

theorem left_transition_of_nat (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+1+write.toNat) :
    actionLookup (q : V) (digit read) = 4*(target : V)+1+digit write := by
  have h := actionLookup_numeral (V := V) q read.toNat
  rw [hrow] at h
  cases read <;> cases write <;> simpa [digit, numeral_eq_natCast] using h

theorem step_right_numeral (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+3+write.toNat) (left suffix : V) :
    stepValue (frame (q : V) left (2*suffix+digit read)) =
      frame (target : V) (2*left+digit write) suffix :=
  step_right_row read write (q : V) (target : V)
    (right_transition_of_nat read write q target hrow) left suffix

theorem step_left_numeral (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+1+write.toNat) (left suffix : V) :
    stepValue (frame (q : V) left (2*suffix+digit read)) =
      leftFrame (target : V) left (2*suffix+digit write) :=
  step_left_row read write (q : V) (target : V)
    (left_transition_of_nat read write q target hrow) left suffix

theorem step_right_run (read write : Bool) (state : V)
    (hrow : actionLookup state (digit read) = 4*state+3+digit write)
    (length left right : V) :
    stepValue (frame state left (bitPrefix read (length+1) right)) =
      frame state (2*left+digit write) (bitPrefix read length right) := by
  rw [bitPrefix_succ, step_right_row read write state state hrow]

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

/-- Π₁ induction permits both full tape parameters to change across a step. -/
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

theorem scan_right_numeral (read write : Bool) (state : Nat)
    (hrow : lookupNat literalRows 0 state read.toNat = 4*state+3+write.toNat)
    (length left right : V) :
    runFrom length (frame (state : V) left (bitPrefix read length right)) =
      frame (state : V) (bitPrefix write length left) right :=
  scan_right read write (state : V)
    (right_transition_of_nat read write state state hrow) length left right

theorem scan_left_numeral (read write : Bool) (state : Nat)
    (hrow : lookupNat literalRows 0 state read.toNat = 4*state+1+write.toNat)
    (length left right : V) :
    runFrom length (leftFrame (state : V) (bitPrefix read length left) right) =
      leftFrame (state : V) left (bitPrefix write length right) :=
  scan_left read write (state : V)
    (left_transition_of_nat read write state state hrow) length left right

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240
