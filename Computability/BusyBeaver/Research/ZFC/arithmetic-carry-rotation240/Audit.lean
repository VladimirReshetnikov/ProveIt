import BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252
open ArithmeticMachineGraphRotation240 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)
open ArithmeticRegisterCarryRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.state_codes
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.registerBlock_expanded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.carry_reverse_snoc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.carry_separator
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.carry_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.seek_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.rollback_pair
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.rollback_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.return_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.return_ones
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240.return_probe

example : carryState = 1 ∧ carryProbeState = 97 ∧ seekState = 65 ∧ seekProbeState = 75 ∧
    rollbackState = 100 ∧ rollbackProbeState = 118 ∧
    returnOnesState = 55 ∧ returnZeroState = 41 := state_codes

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (value suffix : V) :
    registerBlock value suffix = 4 * bitPrefix true value suffix + 2 :=
  registerBlock_expanded value suffix
example (value left : V) :
    2 * carryReverseBlock value left + 1 = reverseBlock value (2 * left + 1) :=
  carry_reverse_snoc value left
example (left suffix : V) :
    runFrom 2 (frame (carryState : V) left (4 * suffix + 2)) =
      frame (carryState : V) (4 * left + 2) suffix := carry_separator left suffix
example (value left suffix : V) :
    runFrom (value + 2) (frame (carryState : V) left (registerBlock value suffix)) =
      frame (carryState : V) (carryReverseBlock value left) suffix :=
  carry_block value left suffix
example (value left suffix : V) :
    runFrom (value + 2) (frame (seekState : V) left (registerBlock value suffix)) =
      frame (seekState : V) (reverseBlock value left) suffix := seek_block value left suffix
example (left right : V) :
    runFrom 2 (leftFrame (rollbackState : V) (4 * left + 2) right) =
      leftFrame (rollbackState : V) left (4 * right + 2) := rollback_pair left right
example (value left right : V) :
    runFrom (value + 2)
        (leftFrame (rollbackState : V) (carryReverseBlock value left) right) =
      leftFrame (rollbackState : V) left (registerBlock value right) :=
  rollback_block value left right
example (entry value left right : V)
    (hentry : actionLookup entry (digit true) =
      4 * (returnOnesState : V) + 1 + digit true) :
    runFrom (value + 2) (leftFrame entry (reverseBlock value left) right) =
      leftFrame (returnZeroState : V) left (registerBlock value right) :=
  return_block entry hentry value left right
example (value left right : V) :
    runFrom (value + 2)
        (leftFrame (returnOnesState : V) (reverseBlock value left) right) =
      leftFrame (returnZeroState : V) left (registerBlock value right) :=
  return_ones value left right
example (value left right : V) :
    runFrom (value + 2)
        (leftFrame (returnZeroState : V) (reverseBlock value left) right) =
      leftFrame (returnZeroState : V) left (registerBlock value right) :=
  return_probe value left right

-- Zero-valued blocks exercise the two-row cases without requiring positivity.
example (left suffix : V) :
    runFrom 2 (frame (carryState : V) left (registerBlock 0 suffix)) =
      frame (carryState : V) (carryReverseBlock 0 left) suffix := by
  simpa only [zero_add] using carry_block (0 : V) left suffix
example (left right : V) :
    runFrom 2 (leftFrame (rollbackState : V) (carryReverseBlock 0 left) right) =
      leftFrame (rollbackState : V) left (registerBlock 0 right) := by
  simpa only [zero_add] using rollback_block (0 : V) left right

end Internal
