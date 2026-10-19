import BusyBeaver.ZFC.ArithmeticDecrementRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticRegisterCarryRotation240 ArithmeticOneRegisterBlocksRotation240
open ArithmeticCarryTraversalRotation240 ArithmeticEndPulseRotation240
open ArithmeticDecrementRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.zero_restore
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.registerBlock_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.zero_decrement_next
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.zero_decrement_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.zero_decrement_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.positive_test
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.return_carried_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.positive_decrement_boundary
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.leftFrame_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.positive_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.positive_decrement_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240.decrement_clocks_positive

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (left suffix : V) :
    runFrom 5 (frame (testState : V) (4*left+2) (4*suffix+2)) =
      leftFrame (rollbackState : V) left (4*(4*suffix+2)+2) := zero_restore left suffix
example (suffix : V) : registerBlock (0 : V) suffix = 4*suffix+2 := registerBlock_zero suffix
example (pre : List V) (next left suffix : V) :
    runFrom (2*fileClock pre+7)
        (frame (carryState : V) left (fileTape pre (4*registerBlock next suffix))) =
      leftFrame (rollbackState : V) left
        (fileTape pre (registerBlock 0 (registerBlock next suffix))) :=
  zero_decrement_next pre next left suffix
example (pre rest : List V) (next count left right : V) :
    runFrom (2*fileClock pre+7)
        (frame (carryState : V) left
          (fileTape pre (4*registerBlock next (fileTape rest (oneBlocks count right))))) =
      leftFrame (rollbackState : V) left
        (fileTape pre
          (registerBlock 0 (registerBlock next (fileTape rest (oneBlocks count right))))) :=
  zero_decrement_file pre rest next count left right
example (pre : List V) (count left right : V) :
    runFrom (2*fileClock pre+7)
        (frame (carryState : V) left (fileTape pre (4*oneBlocks (count+1) right))) =
      leftFrame (rollbackState : V) left
        (fileTape pre (registerBlock 0 (oneBlocks (count+1) right))) :=
  zero_decrement_spares pre count left right
example (value left suffix : V) :
    runFrom 2
        (frame (testState : V) (4*left+2) (bitPrefix true (value+1) suffix)) =
      leftFrame (returnZeroState : V) (2*left+1) (registerBlock value suffix) :=
  positive_test value left suffix
example (pre : List V) (left right : V) :
    runFrom (fileClock pre)
        (leftFrame (returnZeroState : V) (2*carriedFile pre left+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (fileTape pre right) :=
  return_carried_prefix pre left right
example (pre : List V) (value left suffix : V) :
    runFrom (2*fileClock pre+4)
        (frame (carryState : V) left
          (fileTape pre (4*bitPrefix true (value+1) suffix))) =
      leftFrame (returnZeroState : V) (2*left+1)
        (fileTape pre (registerBlock value suffix)) :=
  positive_decrement_boundary pre value left suffix
example (state left right : V) :
    leftFrame state (2*left+1) right = frame state left (2*right+1) :=
  leftFrame_one state left right
example (pre : List V) (value left suffix : V) :
    runFrom (2*fileClock pre+4)
        (frame (carryState : V) left
          (fileTape pre (4*bitPrefix true (value+1) suffix))) =
      frame (returnZeroState : V) left (2*fileTape pre (registerBlock value suffix)+1) :=
  positive_decrement pre value left suffix
example (pre rest : List V) (value count left right : V) :
    runFrom (2*fileClock pre+4)
        (frame (carryState : V) left
          (fileTape pre (4*bitPrefix true (value+1) (fileTape rest (oneBlocks count right))))) =
      frame (returnZeroState : V) left
        (2*fileTape pre (registerBlock value (fileTape rest (oneBlocks count right)))+1) :=
  positive_decrement_file pre rest value count left right
example (pre : List V) :
    0 < 2*fileClock pre+4 ∧ 0 < 2*fileClock pre+7 := decrement_clocks_positive pre

-- The selected first register permits an empty crossed prefix in either branch.
example (value left suffix : V) :
    runFrom 4 (frame (carryState : V) left (4*bitPrefix true (value+1) suffix)) =
      frame (returnZeroState : V) left (2*registerBlock value suffix+1) := by
  simpa only [fileClock, fileTape, mul_zero, zero_add] using
    positive_decrement ([] : List V) value left suffix
example (left right : V) :
    runFrom 7 (frame (carryState : V) left (4*oneBlocks (0+1) right)) =
      leftFrame (rollbackState : V) left (registerBlock 0 (oneBlocks (0+1) right)) := by
  simpa only [fileClock, fileTape, mul_zero, zero_add] using
    zero_decrement_spares ([] : List V) (0 : V) left right
