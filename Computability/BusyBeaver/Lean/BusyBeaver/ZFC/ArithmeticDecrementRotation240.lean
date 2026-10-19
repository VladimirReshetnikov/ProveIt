import BusyBeaver.ZFC.ArithmeticEndPulseRotation240
import BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240

set_option autoImplicit false

/-!
Exact Rotation240 zero and positive marked-target decrement endpoints.
The finite prefix contains arbitrary internal register values. Both complete
numeric tape contexts, all following values and the spare count remain free.
Positive decrement moves the file boundary right one cell and appends no spare.
The zero branch requires a following ordinary block; one remaining value-one
spare suffices when the selected target is the last physical register.
These endpoints use no first-exit hypothesis and assert no dispatch theorem.
The contracts follow Rotation240Boxes. Mira-Cult, Jeff Ketchersid,
Andrew James Wade and ProveIt retain their attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 (lookupNat)
open ArithmeticMachineGraphRotation240 ArithmeticMachineStepRotation240
open ArithmeticMachineRunFromRotation240 ArithmeticMachineUniformScansPerm252
open ArithmeticMachineScansRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)
open ArithmeticRegisterCarryRotation240 ArithmeticOneRegisterBlocksRotation240
open ArithmeticCarryTraversalRotation240 ArithmeticEndPulseRotation240

private theorem test_one : lookupNat literalRows 0 testState 1 =
    4*returnOnesState+2 := by decide +kernel
private theorem return_zero : lookupNat literalRows 0 returnOnesState 0 =
    4*returnZeroState+1 := by decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A marked zero is restored using the first 01 of the following block. -/
theorem zero_restore (left suffix : V) :
    runFrom 5 (frame (testState : V) (4*left+2) (4*suffix+2)) =
      leftFrame (rollbackState : V) left (4*(4*suffix+2)+2) := by
  conv_lhs => arg 1; rw [show (5 : V) = 3+2 by ring]
  rw [runFrom_add, pulse_zero_one, rollback_pair]

theorem registerBlock_zero (suffix : V) : registerBlock (0 : V) suffix = 4*suffix+2 := by
  rw [registerBlock_expanded, bitPrefix_zero]

/-- The next block can hold any internal value and retain any complete suffix. -/
theorem zero_decrement_next (pre : List V) (next left suffix : V) :
    runFrom (2*fileClock pre+7)
        (frame (carryState : V) left (fileTape pre (4*registerBlock next suffix))) =
      leftFrame (rollbackState : V) left
        (fileTape pre (registerBlock 0 (registerBlock next suffix))) := by
  have localRun : runFrom 5
        (frame (testState : V) (4*carriedFile pre left+2) (registerBlock next suffix)) =
      leftFrame (rollbackState : V) (carriedFile pre left)
        (registerBlock 0 (registerBlock next suffix)) := by
    rw [registerBlock_zero]
    simpa only [registerBlock_expanded] using
      zero_restore (carriedFile pre left) (bitPrefix true next suffix)
  conv_lhs => arg 1; rw [show (2*fileClock pre+7 : V) =
    fileClock pre+(2+(5+fileClock pre)) by ring]
  rw [runFrom_add, carry_file, runFrom_add, carry_to_test,
    runFrom_add, localRun, rollback_file]

theorem zero_decrement_file (pre rest : List V) (next count left right : V) :
    runFrom (2*fileClock pre+7)
        (frame (carryState : V) left
          (fileTape pre (4*registerBlock next (fileTape rest (oneBlocks count right))))) =
      leftFrame (rollbackState : V) left
        (fileTape pre
          (registerBlock 0 (registerBlock next (fileTape rest (oneBlocks count right))))) :=
  zero_decrement_next pre next left (fileTape rest (oneBlocks count right))

/-- A final physical zero target is safe when at least one one-valued spare follows. -/
theorem zero_decrement_spares (pre : List V) (count left right : V) :
    runFrom (2*fileClock pre+7)
        (frame (carryState : V) left (fileTape pre (4*oneBlocks (count+1) right))) =
      leftFrame (rollbackState : V) left
        (fileTape pre (registerBlock 0 (oneBlocks (count+1) right))) := by
  have next : oneBlocks (count+1) right = registerBlock 1 (oneBlocks count right) := by
    rw [oneBlocks_succ, registerBlock_one]
  rw [next]
  exact zero_decrement_next pre (1 : V) left (oneBlocks count right)

/-- The two positive-test rows retain every cell after the remaining unary value. -/
theorem positive_test (value left suffix : V) :
    runFrom 2
        (frame (testState : V) (4*left+2) (bitPrefix true (value+1) suffix)) =
      leftFrame (returnZeroState : V) (2*left+1) (registerBlock value suffix) := by
  have first : stepValue
        (frame (testState : V) (4*left+2) (bitPrefix true (value+1) suffix)) =
      leftFrame (returnOnesState : V) (4*left+2) (bitPrefix true (value+1) suffix) := by
    simpa only [bitPrefix_succ] using
      step_left_numeral true true testState returnOnesState test_one
        (4*left+2) (bitPrefix true value suffix)
  have second : stepValue
        (leftFrame (returnOnesState : V) (4*left+2) (bitPrefix true (value+1) suffix)) =
      leftFrame (returnZeroState : V) (2*left+1) (registerBlock value suffix) := by
    simpa only [registerBlock, digit, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*left+1) : V) = 4*left+2 by ring] using
      step_left_recenter false false (returnOnesState : V) (returnZeroState : V)
        (left_transition_of_nat false false returnOnesState returnZeroState return_zero)
        (2*left+1) (bitPrefix true (value+1) suffix)
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second]

/-- The final carried one changes the crossed prefix into ordinary return blocks. -/
theorem return_carried_prefix (pre : List V) (left right : V) :
    runFrom (fileClock pre)
        (leftFrame (returnZeroState : V) (2*carriedFile pre left+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (fileTape pre right) := by
  induction pre generalizing left right with
  | nil => simp only [fileClock, carriedFile, fileTape, runFrom_zero]
  | cons value pre ih =>
    simp only [fileClock, carriedFile, fileTape]
    conv_lhs => arg 1; rw [add_comm]
    rw [runFrom_add, ih, carry_reverse_snoc, return_probe]

/-- Positive input value+1 becomes value; the complete arbitrary suffix is untouched. -/
theorem positive_decrement_boundary (pre : List V) (value left suffix : V) :
    runFrom (2*fileClock pre+4)
        (frame (carryState : V) left
          (fileTape pre (4*bitPrefix true (value+1) suffix))) =
      leftFrame (returnZeroState : V) (2*left+1)
        (fileTape pre (registerBlock value suffix)) := by
  conv_lhs => arg 1; rw [show (2*fileClock pre+4 : V) =
    fileClock pre+(2+(2+fileClock pre)) by ring]
  rw [runFrom_add, carry_file, runFrom_add, carry_to_test,
    runFrom_add, positive_test, return_carried_prefix]

theorem leftFrame_one (state left right : V) :
    leftFrame state (2*left+1) right = frame state left (2*right+1) := by
  have hd : (2*left+1)/2 = left := by
    simpa only [digit, if_true] using digit_div_two true left
  have hm : (2*left+1)%2 = (1 : V) := by
    simpa only [digit, if_true] using digit_mod_two true left
  unfold leftFrame
  rw [hd, hm]
  congr 1
  ring

/-- Same origin-facing endpoint: the one added before the file is explicit. -/
theorem positive_decrement (pre : List V) (value left suffix : V) :
    runFrom (2*fileClock pre+4)
        (frame (carryState : V) left
          (fileTape pre (4*bitPrefix true (value+1) suffix))) =
      frame (returnZeroState : V) left (2*fileTape pre (registerBlock value suffix)+1) := by
  rw [positive_decrement_boundary, leftFrame_one]

theorem positive_decrement_file (pre rest : List V) (value count left right : V) :
    runFrom (2*fileClock pre+4)
        (frame (carryState : V) left
          (fileTape pre (4*bitPrefix true (value+1) (fileTape rest (oneBlocks count right))))) =
      frame (returnZeroState : V) left
        (2*fileTape pre (registerBlock value (fileTape rest (oneBlocks count right)))+1) :=
  positive_decrement pre value left (fileTape rest (oneBlocks count right))

theorem decrement_clocks_positive (pre : List V) :
    0 < 2*fileClock pre+4 ∧ 0 < 2*fileClock pre+7 := by
  constructor
  · rw [show (2*fileClock pre+4 : V) = (2*fileClock pre+3)+1 by ring]
    simp
  · rw [show (2*fileClock pre+7 : V) = (2*fileClock pre+6)+1 by ring]
    simp

end SetTheory.BusyBeaver.ZFC.ArithmeticDecrementRotation240
