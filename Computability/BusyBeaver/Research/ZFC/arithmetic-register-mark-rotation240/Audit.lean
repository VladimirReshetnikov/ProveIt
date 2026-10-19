import BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticMachineGraphRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)
open ArithmeticOneRegisterBlocksRotation240 ArithmeticCarryTraversalRotation240
open ArithmeticIncrementRotation240 (reverseFile)
open ArithmeticRegisterMarkRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.state_codes
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.skip_state_code
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.skip_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.skip_next
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.skip_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.skip_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.mark_steps
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.return_mark_block
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.return_mark_target
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.return_mark_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.mark_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.mark_file_spares
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.markExitCode_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.markExit_state_code
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240.mark_clock_positive

example : (List.range 9).map skipCode = [52,37,26,49,33,34,23,56,61] ∧
    restoreCode = 17 ∧ markFirstCode = 2 ∧ markOnesCode = 3 ∧ markZeroCode = 4 := state_codes
example (j : Nat) :
    ArithmeticMachinePerm252.stateCode (some (RegisterMarkRotation240.skip j)) = skipCode j :=
  skip_state_code j

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (j : Nat) (hj : j < 9) :
    actionLookup (skipCode j : V) (digit true) = 4*(skipCode j : V)+3+digit true :=
  skip_one j hj
example (j : Nat) (hj : j < 8) :
    actionLookup (skipCode (j+1) : V) (digit false) = 4*(skipCode j : V)+3+digit false :=
  skip_next j hj
example (j : Nat) (hj : j < 8) (value left right : V) :
    runFrom (value+2) (frame (skipCode (j+1) : V) left (registerBlock value right)) =
      frame (skipCode j : V) (reverseBlock value left) right := skip_block j hj value left right
example (pre : List V) (hp : pre.length < 9) (left right : V) :
    runFrom (fileClock pre) (frame (skipCode pre.length : V) left (fileTape pre right)) =
      frame (skipCode 0 : V) (reverseFile pre left) right := skip_file pre hp left right
example (value left right : V) :
    runFrom 3 (frame (skipCode 0 : V) left (registerBlock value right)) =
      leftFrame (markFirstCode : V) left (4*bitPrefix true value right) := mark_steps value left right
example (entry : V)
    (hentry : actionLookup entry (digit true) = 4*(markOnesCode : V)+1+digit true)
    (value left right : V) :
    runFrom (value+2) (leftFrame entry (reverseBlock value left) right) =
      leftFrame (markZeroCode : V) left (registerBlock value right) :=
  return_mark_block entry hentry value left right
example (rest : List V) (entry value left right : V)
    (hentry : actionLookup entry (digit true) = 4*(markOnesCode : V)+1+digit true) :
    runFrom (fileClock rest+value+2)
        (leftFrame entry (reverseFile rest (reverseBlock value left)) right) =
      leftFrame (markZeroCode : V) left (registerBlock value (fileTape rest right)) :=
  return_mark_target rest entry value left right hentry
example (pre : List V) (left right : V) :
    runFrom (fileClock pre) (leftFrame (markFirstCode : V) (reverseFile pre left) right) =
      leftFrame (markExitCode pre : V) left (fileTape pre right) := return_mark_prefix pre left right
example (pre : List V) (hp : pre.length < 9) (value left right : V) :
    runFrom (2*fileClock pre+3)
        (frame (skipCode pre.length : V) left (fileTape pre (registerBlock value right))) =
      leftFrame (markExitCode pre : V) left (fileTape pre (4*bitPrefix true value right)) :=
  mark_file pre hp value left right
example (pre rest : List V) (hp : pre.length < 9) (value count left right : V) :
    runFrom (2*fileClock pre+3)
        (frame (skipCode pre.length : V) left
          (fileTape pre (registerBlock value (fileTape rest (oneBlocks count right))))) =
      leftFrame (markExitCode pre : V) left
        (fileTape pre (4*bitPrefix true value (fileTape rest (oneBlocks count right)))) :=
  mark_file_spares pre rest hp value count left right
example (pre : List V) (r : Fin 9) (hr : pre.length = r.val) :
    markExitCode pre = if r.val = 0 then markFirstCode else markZeroCode :=
  markExitCode_split pre r hr
example (pre : List V) :
    ArithmeticMachinePerm252.stateCode (some
      (if pre.length = 0 then RegisterMarkRotation240.markFirst
       else RegisterMarkRotation240.markReturnZero)) = markExitCode pre := markExit_state_code pre
example (pre : List V) : 0 < 2*fileClock pre+3 := mark_clock_positive pre

-- The first physical register has no preceding blocks and retains either full tail.
example (value left right : V) :
    runFrom 3 (frame (skipCode 0 : V) left (registerBlock value right)) =
      leftFrame (markFirstCode : V) left (4*bitPrefix true value right) := by
  simpa only [fileClock, fileTape, List.length_nil, markExitCode, mul_zero, zero_add] using
    mark_file ([] : List V) (by change 0 < 9; decide) value left right
-- Canonical startup spares plus an arbitrary internal excess are unchanged.
example (pre rest : List V) (hp : pre.length < 9) (value extra left right : V) :
    runFrom (2*fileClock pre+3)
        (frame (skipCode pre.length : V) left
          (fileTape pre (registerBlock value (fileTape rest (oneBlocks (167+extra) right))))) =
      leftFrame (markExitCode pre : V) left
        (fileTape pre (4*bitPrefix true value (fileTape rest (oneBlocks (167+extra) right)))) :=
  mark_file_spares pre rest hp value (167+extra) left right
