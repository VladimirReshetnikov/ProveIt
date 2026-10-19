import BusyBeaver.ZFC.ArithmeticIncrementRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)
open ArithmeticRegisterCarryRotation240 ArithmeticOneRegisterBlocksRotation240
open ArithmeticCarryTraversalRotation240 ArithmeticIncrementRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.return_carried_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.return_carried_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.shift_suffix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.return_shifted_suffix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.shifted_target_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.appended_spare
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.increment_suffix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.seek_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.return_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.increment_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240.increment_clock_positive

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (count left right : V) :
    runFrom (3*count)
        (leftFrame (returnZeroState : V) (2*carriedSpares count left+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (oneBlocks count right) :=
  return_carried_spares count left right
example (values : List V) (left right : V) :
    runFrom (fileClock values)
        (leftFrame (returnZeroState : V) (2*carriedFile values left+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (fileTape values right) :=
  return_carried_file values left right
example (rest : List V) (value count left : V) :
    runFrom (value+fileClock rest+3*count+6)
        (frame (carryState : V) left
          (bitPrefix true value (fileTape rest (oneBlocks count 0)))) =
      leftFrame (returnZeroState : V)
        (2*carriedSpares count (carriedFile rest (bitPrefix true value left))+1) 6 :=
  shift_suffix rest value count left
example (rest : List V) (count left right : V) :
    runFrom (3*count+fileClock rest)
        (leftFrame (returnZeroState : V)
          (2*carriedSpares count (carriedFile rest left)+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (fileTape rest (oneBlocks count right)) :=
  return_shifted_suffix rest count left right
example (value left : V) :
    2*bitPrefix true value (4*left+1)+1 = reverseBlock (value+1) left :=
  shifted_target_left value left
example (count : V) : oneBlocks count 6 = oneBlocks (count+1) 0 := appended_spare count
example (rest : List V) (value count left : V) :
    runFrom (2*value+2*fileClock rest+6*count+11)
        (frame (seekState : V) left
          (4*bitPrefix true value (fileTape rest (oneBlocks count 0)))) =
      leftFrame (returnZeroState : V) left
        (registerBlock (value+1) (fileTape rest (oneBlocks (count+1) 0))) :=
  increment_suffix rest value count left
example (values : List V) (left right : V) :
    runFrom (fileClock values) (frame (seekState : V) left (fileTape values right)) =
      frame (seekState : V) (reverseFile values left) right := seek_file values left right
example (values : List V) (left right : V) :
    runFrom (fileClock values)
        (leftFrame (returnZeroState : V) (reverseFile values left) right) =
      leftFrame (returnZeroState : V) left (fileTape values right) := return_file values left right
example (pre rest : List V) (value count left : V) :
    runFrom (2*fileClock pre+2*value+2*fileClock rest+6*count+11)
        (frame (seekState : V) left
          (fileTape pre (4*bitPrefix true value (fileTape rest (oneBlocks count 0))))) =
      leftFrame (returnZeroState : V) left
        (fileTape pre (registerBlock (value+1) (fileTape rest (oneBlocks (count+1) 0)))) :=
  increment_file pre rest value count left
example (pre rest : List V) (value count : V) :
    0 < 2*fileClock pre+2*value+2*fileClock rest+6*count+11 :=
  increment_clock_positive pre rest value count

-- No intervening suffix registers or positive spare-count premise is needed.
example (value count left : V) :
    runFrom (2*value+6*count+11)
        (frame (seekState : V) left (4*bitPrefix true value (oneBlocks count 0))) =
      leftFrame (returnZeroState : V) left (registerBlock (value+1) (oneBlocks (count+1) 0)) := by
  simpa only [fileClock, fileTape, mul_zero, add_zero] using increment_suffix [] value count left
-- The startup's 167 spares may be extended by an arbitrary internal amount.
example (pre rest : List V) (value extra left : V) :
    runFrom (2*fileClock pre+2*value+2*fileClock rest+6*(167+extra)+11)
        (frame (seekState : V) left
          (fileTape pre (4*bitPrefix true value (fileTape rest (oneBlocks (167+extra) 0))))) =
      leftFrame (returnZeroState : V) left
        (fileTape pre (registerBlock (value+1) (fileTape rest (oneBlocks ((167+extra)+1) 0)))) :=
  increment_file pre rest value (167+extra) left
