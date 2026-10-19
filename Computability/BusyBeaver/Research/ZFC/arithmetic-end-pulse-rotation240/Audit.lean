import BusyBeaver.ZFC.ArithmeticEndPulseRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterCarryRotation240 ArithmeticEndPulseRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.pulse_state_codes
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.restore_mark
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.pulse_zero_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.pulse_zero_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.carry_to_test
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.carry_end_window
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.carry_end
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240.carry_ones

example : testState = 67 ∧ pulseState = 240 := pulse_state_codes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (left suffix : V) :
    runFrom 2 (frame (seekState : V) left (4*suffix)) =
      frame (carryState : V) (4*left+1) suffix := restore_mark left suffix
example (left suffix : V) :
    runFrom 3 (frame (testState : V) left (4*suffix)) =
      leftFrame (rollbackProbeState : V) left (4*suffix+3) := pulse_zero_zero left suffix
example (left suffix : V) :
    runFrom 3 (frame (testState : V) left (4*suffix+2)) =
      leftFrame (rollbackState : V) left (4*suffix+2) := pulse_zero_one left suffix
example (left suffix : V) :
    runFrom 2 (frame (carryState : V) left (4*suffix)) =
      frame (testState : V) (4*left+2) suffix := carry_to_test left suffix
example (left suffix : V) :
    runFrom 6 (frame (carryState : V) left (16*suffix)) =
      leftFrame (returnZeroState : V) (2*left+1) (8*suffix+6) := carry_end_window left suffix
example (left : V) :
    runFrom 6 (frame (carryState : V) left 0) =
      leftFrame (returnZeroState : V) (2*left+1) 6 := carry_end left
example (length left right : V) :
    runFrom length (frame (carryState : V) left (bitPrefix true length right)) =
      frame (carryState : V) (bitPrefix true length left) right := carry_ones length left right
