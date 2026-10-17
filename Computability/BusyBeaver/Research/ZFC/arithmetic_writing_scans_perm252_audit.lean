import BusyBeaver.ZFC.ArithmeticWritingScansPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252.step_right_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252.step_left_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252.scan_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252.scan_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252.scan_right_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticWritingScansPerm252.scan_left_numeral
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (read write : Bool) (state length left right : V)
    (hrow : actionLookup state (digit read) = 4*state+3+digit write) :
    stepValue (frame state left (bitPrefix read (length+1) right)) =
      frame state (2*left+digit write) (bitPrefix read length right) :=
  ArithmeticWritingScansPerm252.step_right_run read write state hrow length left right
example (read write : Bool) (state length left right : V)
    (hrow : actionLookup state (digit read) = 4*state+1+digit write) :
    stepValue (leftFrame state (bitPrefix read (length+1) left) right) =
      leftFrame state (bitPrefix read length left) (2*right+digit write) :=
  ArithmeticWritingScansPerm252.step_left_run read write state hrow length left right
example (read write : Bool) (state length left right : V)
    (hrow : actionLookup state (digit read) = 4*state+3+digit write) :
    runFrom length (frame state left (bitPrefix read length right)) =
      frame state (bitPrefix write length left) right :=
  ArithmeticWritingScansPerm252.scan_right read write state hrow length left right
example (read write : Bool) (state length left right : V)
    (hrow : actionLookup state (digit read) = 4*state+1+digit write) :
    runFrom length (leftFrame state (bitPrefix read length left) right) =
      leftFrame state left (bitPrefix write length right) :=
  ArithmeticWritingScansPerm252.scan_left read write state hrow length left right
example (read write : Bool) (state : Nat) (length left right : V)
    (hrow : lookupNat literalRows 0 state read.toNat = 4*state+3+write.toNat) :
    runFrom length (frame (state : V) left (bitPrefix read length right)) =
      frame (state : V) (bitPrefix write length left) right :=
  ArithmeticWritingScansPerm252.scan_right_numeral read write state hrow length left right
example (read write : Bool) (state : Nat) (length left right : V)
    (hrow : lookupNat literalRows 0 state read.toNat = 4*state+1+write.toNat) :
    runFrom length (leftFrame (state : V) (bitPrefix read length left) right) =
      leftFrame (state : V) left (bitPrefix write length right) :=
  ArithmeticWritingScansPerm252.scan_left_numeral read write state hrow length left right
example (length left right : V) :
    runFrom length (leftFrame 8 (bitPrefix true length left) right) =
      leftFrame 8 left (bitPrefix false length right) := by
  simpa only [Nat.cast_ofNat] using
    ArithmeticWritingScansPerm252.scan_left_numeral true false 8 (by decide) length left right
example (length left right : V) :
    runFrom length (frame 14 left (bitPrefix true length right)) =
      frame 14 (bitPrefix false length left) right := by
  simpa only [Nat.cast_ofNat] using
    ArithmeticWritingScansPerm252.scan_right_numeral true false 14 (by decide) length left right
example (length left right : V) :
    runFrom length (frame 42 left (bitPrefix false length right)) =
      frame 42 (bitPrefix true length left) right := by
  simpa only [Nat.cast_ofNat] using
    ArithmeticWritingScansPerm252.scan_right_numeral false true 42 (by decide) length left right
example (read write : Bool) (state left right : V)
    (hrow : actionLookup state (digit read) = 4*state+3+digit write) :
    runFrom 0 (frame state left right) = frame state left right := by
  simpa using ArithmeticWritingScansPerm252.scan_right read write state hrow (0 : V) left right
example (read write : Bool) (state left right : V)
    (hrow : actionLookup state (digit read) = 4*state+1+digit write) :
    runFrom 0 (leftFrame state left right) = leftFrame state left right := by
  simpa using ArithmeticWritingScansPerm252.scan_left read write state hrow (0 : V) left right
example (b : Bool) (state length left right : V)
    (hrow : actionLookup state (digit b) = 4*state+3+digit b) :
    runFrom length (frame state left (bitPrefix b length right)) =
      frame state (bitPrefix b length left) right :=
  ArithmeticWritingScansPerm252.scan_right b b state hrow length left right
