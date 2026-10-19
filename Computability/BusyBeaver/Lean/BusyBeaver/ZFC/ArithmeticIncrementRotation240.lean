import BusyBeaver.ZFC.ArithmeticEndPulseRotation240
import BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240

set_option autoImplicit false

/-!
Marked-target increment with a finite prefix/suffix of arbitrary internal
register values and an arbitrary internal number of value-one spares.
The complete left tape is arbitrary; the right exterior after the spares is
blank. Exactly one new 011 spare is appended. All steps use Rotation240.
This is an endpoint contract, not a first-exit or full dispatch simulation.
The construction follows Rotation240Boxes.increment_zip and the earlier
arithmetic finite-file framework, with Rotation240's six-step end pulse and
value-one spares. Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt
retain their attribution. The two imported new units require separate checks.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252 ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)
open ArithmeticRegisterCarryRotation240 ArithmeticOneRegisterBlocksRotation240
open ArithmeticCarryTraversalRotation240 ArithmeticEndPulseRotation240

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance carriedSpares_delta : 𝚫₁-Function₂[V] carriedSpares :=
  carriedSpares_defined_delta.to_definable
private instance oneBlocks_delta : 𝚫₁-Function₂[V] oneBlocks :=
  oneBlocks_defined_delta.to_definable
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom :=
  runFrom_defined_delta.to_definable
private instance frame_delta : 𝚫₁-Function₃[V] frame :=
  frame_defined.graph_delta.to_definable
private instance leftFrame_delta : 𝚫₁-Function₃[V] leftFrame := by
  unfold leftFrame
  definability

private def ReturnCarriedSpares (count : V) : Prop := ∀ left right : V,
  runFrom (3*count)
      (leftFrame (returnZeroState : V) (2*carriedSpares count left+1) right) =
    leftFrame (returnZeroState : V) (2*left+1) (oneBlocks count right)
private instance returnCarriedSpares_definable :
    𝚷₁-Predicate (ReturnCarriedSpares (V := V)) := by
  unfold ReturnCarriedSpares
  definability

/-- The pulse's final carried one normalizes every crossed spare for return. -/
theorem return_carried_spares (count left right : V) :
    runFrom (3*count)
        (leftFrame (returnZeroState : V) (2*carriedSpares count left+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (oneBlocks count right) := by
  have allCounts : ∀ count : V, ReturnCarriedSpares count := by
    intro count
    induction count using ISigma1.pi1_succ_induction
    · exact returnCarriedSpares_definable
    case zero =>
      intro left right
      simp only [mul_zero, runFrom_zero, carriedSpares_zero, oneBlocks_zero]
    case succ count ih =>
      intro left right
      have block : 2*carriedSpares (count+1) left+1 =
          reverseBlock 1 (2*carriedSpares count left+1) := by
        rw [show carriedSpares (count+1) left =
          carryReverseBlock 1 (carriedSpares count left) by
            rw [carriedSpares_succ, carryReverseBlock_one], carry_reverse_snoc]
      conv_lhs => arg 1; rw [show (3*(count+1) : V) = (1+2)+3*count by ring]
      rw [block, runFrom_add, return_probe, registerBlock_one, ih, oneBlocks_push]
  exact allCounts count left right

theorem return_carried_file (values : List V) (left right : V) :
    runFrom (fileClock values)
        (leftFrame (returnZeroState : V) (2*carriedFile values left+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (fileTape values right) := by
  induction values generalizing left right with
  | nil => simp only [fileClock, carriedFile, fileTape, runFrom_zero]
  | cons value values ih =>
    simp only [fileClock, carriedFile, fileTape]
    conv_lhs => arg 1; rw [add_comm]
    rw [runFrom_add, ih, carry_reverse_snoc, return_probe]

/-- Only this forward endpoint specializes the unrepresented exterior to blank. -/
theorem shift_suffix (rest : List V) (value count left : V) :
    runFrom (value+fileClock rest+3*count+6)
        (frame (carryState : V) left
          (bitPrefix true value (fileTape rest (oneBlocks count 0)))) =
      leftFrame (returnZeroState : V)
        (2*carriedSpares count (carriedFile rest (bitPrefix true value left))+1) 6 := by
  conv_lhs => arg 1; rw [show (value+fileClock rest+3*count+6 : V) =
    value+((fileClock rest+3*count)+6) by ring]
  rw [runFrom_add, carry_ones, runFrom_add, carry_file_spares, carry_end]

/-- Return retains any right tape, including the pulse's new 011 block. -/
theorem return_shifted_suffix (rest : List V) (count left right : V) :
    runFrom (3*count+fileClock rest)
        (leftFrame (returnZeroState : V)
          (2*carriedSpares count (carriedFile rest left)+1) right) =
      leftFrame (returnZeroState : V) (2*left+1) (fileTape rest (oneBlocks count right)) := by
  rw [runFrom_add, return_carried_spares, return_carried_file]

theorem shifted_target_left (value left : V) :
    2*bitPrefix true value (4*left+1)+1 = reverseBlock (value+1) left := by
  calc
    2*bitPrefix true value (4*left+1)+1 = bitPrefix true (value+1) (4*left+1) := by
      rw [bitPrefix_succ]
      rfl
    _ = reverseBlock (value+1) left := by
      unfold reverseBlock
      simpa only [digit, if_true, show (2*(2*left)+1 : V) = 4*left+1 by ring] using
        bitPrefix_push true (value+1) (2*left)

theorem appended_spare (count : V) : oneBlocks count 6 = oneBlocks (count+1) 0 := by
  simpa only [mul_zero, zero_add] using oneBlocks_push count (0 : V)

/-- Increment the marked target; all following values are unchanged and one spare is added. -/
theorem increment_suffix (rest : List V) (value count left : V) :
    runFrom (2*value+2*fileClock rest+6*count+11)
        (frame (seekState : V) left
          (4*bitPrefix true value (fileTape rest (oneBlocks count 0)))) =
      leftFrame (returnZeroState : V) left
        (registerBlock (value+1) (fileTape rest (oneBlocks (count+1) 0))) := by
  conv_lhs => arg 1; rw [show (2*value+2*fileClock rest+6*count+11 : V) =
    2+((value+fileClock rest+3*count+6)+((3*count+fileClock rest)+((value+1)+2))) by ring]
  rw [runFrom_add, restore_mark, runFrom_add, shift_suffix,
    runFrom_add, return_shifted_suffix, shifted_target_left, return_probe, appended_spare]

noncomputable def reverseFile : List V → V → V
  | [], left => left
  | value :: values, left => reverseFile values (reverseBlock value left)

theorem seek_file (values : List V) (left right : V) :
    runFrom (fileClock values) (frame (seekState : V) left (fileTape values right)) =
      frame (seekState : V) (reverseFile values left) right := by
  induction values generalizing left with
  | nil => simp only [fileClock, fileTape, reverseFile, runFrom_zero]
  | cons value values ih =>
    simp only [fileClock, fileTape, reverseFile]
    rw [runFrom_add, seek_block, ih]

theorem return_file (values : List V) (left right : V) :
    runFrom (fileClock values)
        (leftFrame (returnZeroState : V) (reverseFile values left) right) =
      leftFrame (returnZeroState : V) left (fileTape values right) := by
  induction values generalizing left right with
  | nil => simp only [fileClock, fileTape, reverseFile, runFrom_zero]
  | cons value values ih =>
    simp only [fileClock, fileTape, reverseFile]
    conv_lhs => arg 1; rw [add_comm]
    rw [runFrom_add, ih, return_probe]

/-- Complete marked-target excursion, with finite physical prefix/suffix and internal spares. -/
theorem increment_file (pre rest : List V) (value count left : V) :
    runFrom (2*fileClock pre+2*value+2*fileClock rest+6*count+11)
        (frame (seekState : V) left
          (fileTape pre (4*bitPrefix true value (fileTape rest (oneBlocks count 0))))) =
      leftFrame (returnZeroState : V) left
        (fileTape pre (registerBlock (value+1) (fileTape rest (oneBlocks (count+1) 0)))) := by
  conv_lhs => arg 1; rw [show (2*fileClock pre+2*value+2*fileClock rest+6*count+11 : V) =
    fileClock pre+((2*value+2*fileClock rest+6*count+11)+fileClock pre) by ring]
  rw [runFrom_add, seek_file, runFrom_add, increment_suffix, return_file]

theorem increment_clock_positive (pre rest : List V) (value count : V) :
    0 < 2*fileClock pre+2*value+2*fileClock rest+6*count+11 := by
  rw [show (2*fileClock pre+2*value+2*fileClock rest+6*count+11 : V) =
    (2*fileClock pre+2*value+2*fileClock rest+6*count+10)+1 by ring]
  simp

end SetTheory.BusyBeaver.ZFC.ArithmeticIncrementRotation240
