import BusyBeaver.ZFC.ArithmeticRegisterFilePerm252

/-!
Positive decrement in the actual frozen252 arithmetic
machine. Values, both whole tape halves and the zero-spare count are internal
IΣ1 model elements. A register list has externally fixed finite length and
arbitrary internal entries. Positive decrement appends one complete zero spare.

This follows the shift_dec_block/shift_dec/box_decp contracts attributed to
mira-emmy PR20 head 0d544f2a2e3c18f12278441a74b7879f31cbe856,
ZF/m253/coq/tm/Box.v, and the maintained RegisterDecrementPerm252 proof.
Mira-Cult, Jeff and Wade retain their machine and framework attributions.
No first-exit, absolute head, dispatch refinement or PA endpoint is asserted.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticZeroSpareScanPerm252
open ArithmeticRegisterIncrementPerm252 ArithmeticRegisterFilePerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance bitPrefix_delta (b : Bool) : 𝚫₁-Function₂[V] (bitPrefix b) :=
  (bitPrefix_defined b).graph_delta.to_definable
private instance zeroBlocks_delta : 𝚫₁-Function₂[V] zeroBlocks :=
  zeroBlocks_defined_delta.to_definable
private instance reverseZeroBlocks_delta : 𝚫₁-Function₂[V] reverseZeroBlocks :=
  reverseZeroBlocks_defined.graph_delta.to_definable
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom :=
  runFrom_defined_delta.to_definable
private instance frame_delta : 𝚫₁-Function₃[V] frame :=
  frame_defined.graph_delta.to_definable

/-- Recenter a nearest-left zero without losing either complete tape half. -/
lemma leftFrame_even (state left right : V) :
    leftFrame state (2*left) right = frame state left (2*right) := by
  unfold leftFrame
  rw [even_div_two, even_mod_two, zero_add]

/-- The literal111/130 pair shifts one complete block left. It keeps the
initial zero on the current cell; the return scanner remains in state111. -/
theorem shift_block (value left right : V) :
    runFrom (value+2) (frame 111 (reverseBlock value left) (2*right)) =
      frame 111 left (2*bitPrefix true value (4*right+2)) := by
  have row : actionLookup (111 : V) (digit true) = 4*111+1+digit true := by
    simpa only [Nat.cast_ofNat] using left_row_of_nat (V := V) true 111 (by decide)
  have first : stepValue (frame 111 (reverseBlock value left) (2*right)) =
      leftFrame 130 (reverseBlock value left) (2*right+1) := by
    simpa [digit] using step_left_numeral false true 111 130 (by decide)
      (reverseBlock value left) right
  have second : stepValue (leftFrame 130 (reverseBlock value left) (2*right+1)) =
      leftFrame 111 (bitPrefix true value (2*left)) (4*right+2) := by
    unfold reverseBlock
    rw [bitPrefix_succ]
    simpa only [digit, if_true, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*right+1) : V) = 4*right+2 by ring] using
      step_left_recenter true false 130 111
        (by simpa only [Nat.cast_ofNat] using
          left_transition_of_nat (V := V) true false 130 111 (by decide))
        (bitPrefix true value (2*left)) (2*right+1)
  rw [show (value+2 : V) = (value+1)+1 by ring,
    runFrom_first, first, runFrom_first, second,
    scan_left true 111 row, leftFrame_even]

/-- Universally quantified whole halves keep the zero-tail induction Π1. -/
def ShiftZeroSpares (count : V) : Prop := ∀ left right : V,
  runFrom (2*count) (frame 111 (reverseZeroBlocks count left) (2*right)) =
    frame 111 left (2*zeroBlocks count right)
private instance shiftZeroSpares_definable : 𝚷₁-Predicate (ShiftZeroSpares (V := V)) := by
  unfold ShiftZeroSpares
  definability

/-- Shifting a variable internal zero tail preserves all of its blocks. -/
theorem shift_zero_spares (count left right : V) :
    runFrom (2*count) (frame 111 (reverseZeroBlocks count left) (2*right)) =
      frame 111 left (2*zeroBlocks count right) := by
  have allCounts : ∀ count : V, ShiftZeroSpares count := by
    intro count
    induction count using ISigma1.pi1_succ_induction
    · exact shiftZeroSpares_definable
    case zero => intro left right; simp
    case succ count ih =>
      intro left right
      have firstBlock :
          runFrom 2 (frame 111 (reverseZeroBlocks (count+1) left) (2*right)) =
            frame 111 (reverseZeroBlocks count left) (2*(4*right+2)) := by
        simpa only [zero_add, bitPrefix_zero, reverseBlock_zero,
          reverseZeroBlocks_succ] using
          shift_block (0 : V) (reverseZeroBlocks count left) right
      rw [show (2*(count+1) : V) = 2+2*count by ring,
        runFrom_add, firstBlock, ih, zeroBlocks_push]
  exact allCounts count left right

/-- While shifting left, a block's zero/one header is temporarily rewoven.
This is an external finite-list fold, not an internal variable-length list. -/
noncomputable def weaveFile : List V → V → V
  | [], right => right
  | value :: rest, right => bitPrefix true value (4*weaveFile rest right+2)

/-- Restoring the one deferred header gives the ordinary register file. -/
theorem weave_file (rest : List V) (right : V) :
    4*weaveFile rest right+2 = fileCode rest (4*right+2) := by
  induction rest with
  | nil => rfl
  | cons value rest ih =>
    change 4*bitPrefix true value (4*weaveFile rest right+2)+2 =
      registerBlock value (fileCode rest (4*right+2))
    rw [ih]
    unfold registerBlock
    rw [bitPrefix_succ]
    simp only [digit, if_true]
    ring

/-- Shift a fixed finite suffix after the internally long zero tail. -/
theorem shift_file_zero_spares (rest : List V) (count left right : V) :
    runFrom (fileTime rest+2*count)
        (frame 111 (reverseZeroBlocks count (reverseFile rest left)) (2*right)) =
      frame 111 left (2*weaveFile rest (zeroBlocks count right)) := by
  induction rest generalizing left right with
  | nil => simpa [fileTime, reverseFile, weaveFile] using
      shift_zero_spares count left right
  | cons value rest ih =>
    simp only [fileTime, reverseFile, weaveFile]
    rw [show (value+2+fileTime rest+2*count : V) =
        (fileTime rest+2*count)+(value+2) by ring,
      runFrom_add, ih, shift_block]

/-- Actual suffix seek/probe84/96 cross a fixed finite register file. -/
theorem forward_suffix_file (rest : List V) (left right : V) :
    runFrom (fileTime rest) (frame 84 left (fileCode rest right)) =
      frame 84 (reverseFile rest left) right := by
  induction rest generalizing left with
  | nil => simp [fileTime, fileCode, reverseFile]
  | cons value rest ih =>
    simp only [fileTime, fileCode, reverseFile]
    rw [runFrom_add, forward_suffix, ih]

/-- Both blank cells are tested before the shift starts at the old head. -/
theorem prepare_shift (left : V) :
    runFrom 2 (frame 84 left 0) = frame 111 left 0 := by
  have first : stepValue (frame 84 left 0) = frame 96 (2*left) 0 := by
    simpa [digit] using step_right_numeral false false 84 96 (by decide) left (0 : V)
  have second : stepValue (frame 96 (2*left) 0) = leftFrame 111 (2*left) 0 := by
    simpa [digit] using step_left_numeral false false 96 111 (by decide)
      (2*left) (0 : V)
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second, leftFrame_even]
  simp

/-- At the marked target's extra zero, finish the shift and retain the added
zero spare header. The output state63 is the ordinary leftward return entry. -/
theorem finish_shift (left right : V) :
    runFrom 2 (frame 111 (2*left) (2*right)) = leftFrame 63 left (4*right+2) := by
  have first : stepValue (frame 111 (2*left) (2*right)) =
      frame 130 left (4*right+2) := by
    have h := step_left_numeral false true 111 130 (by decide) (2*left) right
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero, Nat.cast_ofNat,
      leftFrame_even, show (2*(2*right+1) : V) = 4*right+2 by ring] using h
  have second : stepValue (frame 130 left (4*right+2)) =
      leftFrame 63 left (4*right+2) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero, Nat.cast_ofNat,
      show (2*(2*right+1) : V) = 4*right+2 by ring] using
      step_left_numeral false false 130 63 (by decide) left (2*right+1)
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second]

/-- Three literal rows establish the positive branch: marked00 followed by at
least one one. The remaining value is arbitrary internal. -/
theorem prepare_positive (value left right : V) :
    runFrom 3 (frame 43 left (4*bitPrefix true (value+1) right)) =
      frame 84 (8*left+1) (bitPrefix true value right) := by
  have first : stepValue (frame 43 left (4*bitPrefix true (value+1) right)) =
      frame 59 (2*left) (2*bitPrefix true (value+1) right) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero, Nat.cast_ofNat,
      show (2*(2*bitPrefix true (value+1) right) : V) =
        4*bitPrefix true (value+1) right by ring] using
      step_right_numeral false false 43 59 (by decide) left
        (2*bitPrefix true (value+1) right)
  have second : stepValue (frame 59 (2*left) (2*bitPrefix true (value+1) right)) =
      frame 74 (4*left) (bitPrefix true (value+1) right) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero, Nat.cast_ofNat,
      show (2*(2*left) : V) = 4*left by ring] using
      step_right_numeral false false 59 74 (by decide) (2*left)
        (bitPrefix true (value+1) right)
  have third : stepValue (frame 74 (4*left) (bitPrefix true (value+1) right)) =
      frame 84 (8*left+1) (bitPrefix true value right) := by
    rw [bitPrefix_succ]
    simpa only [digit, if_true, Nat.cast_ofNat, show (2*(4*left)+1 : V) = 8*left+1 by ring] using
      step_right_numeral true true 74 84 (by decide) (4*left) (bitPrefix true value right)
  conv_lhs => arg 1; rw [show (3 : V) = (1+1)+1 by ring]
  rw [runFrom_first, first, runFrom_first, second, runFrom_one, third]

/-- The remembered positive test supplies the target block's final one. -/
theorem target_left (value left : V) :
    bitPrefix true value (8*left+1) = reverseBlock value (2*left) := by
  simpa only [reverseBlock, digit, if_true,
    show (2*(2*(2*left))+1 : V) = 8*left+1 by ring] using
    bitPrefix_push true value (2*(2*left))

/-- Positive decrement with an arbitrary fixed finite suffix and an internal
zero tail. Exactly one zero spare is appended; none is erased or reinterpreted. -/
theorem positive_tail (rest : List V) (value count left : V) :
    runFrom (2*value+2*fileTime rest+4*count+9)
        (frame 43 left
          (4*bitPrefix true (value+1) (fileCode rest (zeroBlocks count 0)))) =
      leftFrame 63 left
        (registerBlock value (fileCode rest (zeroBlocks (count+1) 0))) := by
  have row : actionLookup (84 : V) (digit true) = 4*84+3+digit true :=
    right_row_of_nat true 84 (by decide)
  have shifted :
      runFrom (fileTime rest+2*count)
          (frame 111 (reverseZeroBlocks count
            (reverseFile rest (bitPrefix true value (8*left+1)))) 0) =
        frame 111 (bitPrefix true value (8*left+1))
          (2*weaveFile rest (zeroBlocks count 0)) := by
    simpa only [mul_zero] using
      shift_file_zero_spares rest count (bitPrefix true value (8*left+1)) (0 : V)
  rw [show (2*value+2*fileTime rest+4*count+9 : V) =
      3+(value+(fileTime rest+(2*count+(2+
        ((fileTime rest+2*count)+((value+2)+2)))))) by ring,
    runFrom_add, prepare_positive, runFrom_add, scan_right true 84 row,
    runFrom_add, forward_suffix_file, runFrom_add, scan_zero_blocks_suffix,
    runFrom_add, prepare_shift, runFrom_add, shifted,
    target_left, runFrom_add, shift_block, finish_shift]
  have hh : (4*bitPrefix true value (4*weaveFile rest (zeroBlocks count 0)+2)+2 : V) =
      registerBlock value (fileCode rest (zeroBlocks (count+1) 0)) := by
    have tail : 4*weaveFile rest (zeroBlocks count 0)+2 =
        fileCode rest (zeroBlocks (count+1) 0) := by
      rw [weave_file, zeroBlocks_succ]
    rw [tail]
    unfold registerBlock
    rw [bitPrefix_succ]
    simp only [digit, if_true]
    ring
  rw [hh]

/-- Read past a fixed finite prefix before reaching the marked target. -/
theorem forward_dec_file (pre : List V) (left right : V) :
    runFrom (fileTime pre) (frame 43 left (fileCode pre right)) =
      frame 43 (reverseFile pre left) right := by
  induction pre generalizing left with
  | nil => simp [fileTime, fileCode, reverseFile]
  | cons value pre ih =>
    simp only [fileTime, fileCode, reverseFile]
    rw [runFrom_add, forward_dec, ih]

def positiveExit : List V → V
  | [] => 63
  | _ :: _ => 48

/-- Entry63 is retained if there is no preceding block; otherwise every block
is returned over and the endpoint is separator probe48. -/
theorem return_positive_file (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 63 (reverseFile pre left) right) =
      leftFrame (positiveExit pre) left (fileCode pre right) := by
  cases pre with
  | nil => simp [fileTime, reverseFile, fileCode, positiveExit]
  | cons value pre =>
    have h63 : actionLookup (63 : V) (digit true) = 4*63+2 := by
      simpa only [digit, if_true, Nat.cast_ofNat,
        show (4*63+1+1 : V) = 4*63+2 by ring] using
        left_transition_of_nat (V := V) true true 63 63 (by decide)
    simpa only [fileTime, reverseFile, fileCode, positiveExit,
      mul_zero, add_zero, reverseZeroBlocks_zero, zeroBlocks_zero,
      show (value+2+fileTime pre : V) = fileTime pre+value+2 by ring] using
      return_file_zero_spares pre (63 : V) value (0 : V) left right h63

/-- Full positive marked-target endpoint. The fixed prefix/suffix list values,
marked target and spare count are internal; the external list lengths are fixed. -/
theorem positive_decrement (pre rest : List V) (value count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime rest+4*count+9)
        (frame 43 left (fileCode pre
          (4*bitPrefix true (value+1) (fileCode rest (zeroBlocks count 0))))) =
      leftFrame (positiveExit pre) left (fileCode pre
        (registerBlock value (fileCode rest (zeroBlocks (count+1) 0)))) := by
  rw [show (2*fileTime pre+2*value+2*fileTime rest+4*count+9 : V) =
      fileTime pre+((2*value+2*fileTime rest+4*count+9)+fileTime pre) by ring,
    runFrom_add, forward_dec_file, runFrom_add, positive_tail, return_positive_file]

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252
