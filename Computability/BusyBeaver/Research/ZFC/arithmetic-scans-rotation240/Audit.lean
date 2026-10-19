import BusyBeaver.ZFC.ArithmeticMachineScansRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachineUniformScansPerm252
open ArithmeticMachineGraphPerm252 (lookupNat)
open ArithmeticMachineGraphRotation240 ArithmeticMachineStepRotation240
open ArithmeticMachineRunFromRotation240
open ArithmeticMachineScansRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.step_right_row
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.step_left_row
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.step_left_recenter
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.right_transition_of_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.left_transition_of_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.step_right_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.step_left_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.step_right_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.step_left_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.scan_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.scan_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.scan_right_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScansRotation240.scan_left_numeral

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (read write : Bool) (q target left suffix : V)
    (h : actionLookup q (digit read) = 4*target+3+digit write) :
    stepValue (frame q left (2*suffix+digit read)) =
      frame target (2*left+digit write) suffix := step_right_row read write q target h left suffix
example (read write : Bool) (q target left suffix : V)
    (h : actionLookup q (digit read) = 4*target+1+digit write) :
    stepValue (frame q left (2*suffix+digit read)) =
      leftFrame target left (2*suffix+digit write) := step_left_row read write q target h left suffix
example (read write : Bool) (q target left right : V)
    (h : actionLookup q (digit read) = 4*target+1+digit write) :
    stepValue (leftFrame q (2*left+digit read) right) =
      leftFrame target left (2*right+digit write) := step_left_recenter read write q target h left right
example (read write : Bool) (q target : Nat)
    (h : lookupNat literalRows 0 q read.toNat = 4*target+3+write.toNat) :
    actionLookup (q : V) (digit read) = 4*(target : V)+3+digit write :=
  right_transition_of_nat read write q target h
example (read write : Bool) (q target : Nat)
    (h : lookupNat literalRows 0 q read.toNat = 4*target+1+write.toNat) :
    actionLookup (q : V) (digit read) = 4*(target : V)+1+digit write :=
  left_transition_of_nat read write q target h
example (read write : Bool) (q length left right : V)
    (h : actionLookup q (digit read) = 4*q+3+digit write) :
    runFrom length (frame q left (bitPrefix read length right)) =
      frame q (bitPrefix write length left) right :=
  ArithmeticMachineScansRotation240.scan_right read write q h length left right
example (read write : Bool) (q length left right : V)
    (h : actionLookup q (digit read) = 4*q+1+digit write) :
    runFrom length (leftFrame q (bitPrefix read length left) right) =
      leftFrame q left (bitPrefix write length right) :=
  ArithmeticMachineScansRotation240.scan_left read write q h length left right

-- Literal unchanged scans in both directions, at arbitrary internal lengths.
example (n left right : V) :
    runFrom n (frame 7 left (bitPrefix false n right)) = frame 7 (bitPrefix false n left) right :=
  ArithmeticMachineScansRotation240.scan_right_numeral false false 7 (by decide) n left right
example (n left right : V) :
    runFrom n (frame 1 left (bitPrefix true n right)) = frame 1 (bitPrefix true n left) right := by
  simpa only [Nat.cast_one] using
    ArithmeticMachineScansRotation240.scan_right_numeral true true 1 (by decide) n left right
example (n left right : V) :
    runFrom n (leftFrame 2 (bitPrefix false n left) right) = leftFrame 2 left (bitPrefix false n right) :=
  ArithmeticMachineScansRotation240.scan_left_numeral false false 2 (by decide) n left right
example (n left right : V) :
    runFrom n (leftFrame 3 (bitPrefix true n left) right) = leftFrame 3 left (bitPrefix true n right) :=
  ArithmeticMachineScansRotation240.scan_left_numeral true true 3 (by decide) n left right

-- Actual writing scans exercise different read and written bits.
example (n left right : V) :
    runFrom n (frame 11 left (bitPrefix true n right)) = frame 11 (bitPrefix false n left) right :=
  ArithmeticMachineScansRotation240.scan_right_numeral true false 11 (by decide) n left right
example (n left right : V) :
    runFrom n (frame 36 left (bitPrefix false n right)) = frame 36 (bitPrefix true n left) right :=
  ArithmeticMachineScansRotation240.scan_right_numeral false true 36 (by decide) n left right
example (n left right : V) :
    runFrom n (leftFrame 5 (bitPrefix true n left) right) = leftFrame 5 left (bitPrefix false n right) :=
  ArithmeticMachineScansRotation240.scan_left_numeral true false 5 (by decide) n left right

-- The halt action still writes one and moves right on the whole numeric tape.
example (left suffix : V) :
    stepValue (frame 69 left (2*suffix+1)) = frame 0 (2*left+1) suffix := by
  simpa only [digit, if_true, Nat.cast_ofNat, Nat.cast_zero] using
    step_right_numeral true true 69 0 (by decide) left suffix

end Internal
