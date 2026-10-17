import BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252

/-!
Increment with a fixed finite list of arbitrary internal register values,
followed by an arbitrary internal number of zero spares. The list length is
external; the values, spare count and retained left tape are model elements.
This suffices to describe any fixed tuple of primary registers and the fixed
boot spares, but does not yet give a complete dispatch refinement or first exit.
The suffix-shift/return construction follows the attributed
RegisterIncrementPerm252 contracts and mira-emmy PR20 Box.v. Mira-Cult,
Jeff and Wade retain their machine and verification framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticRegisterReturnPerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticZeroSpareScanPerm252 ArithmeticZeroSpareShiftPerm252
open ArithmeticRegisterIncrementPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def fileCode : List V → V → V
  | [], right => right
  | value :: rest, right => registerBlock value (fileCode rest right)

noncomputable def reverseFile : List V → V → V
  | [], left => left
  | value :: rest, left => reverseFile rest (reverseBlock value left)

def fileTime : List V → V
  | [] => 0
  | value :: rest => value+2+fileTime rest

/-- Seek the marked target through a fixed finite prefix of unmarked registers. -/
theorem forward_inc_file (pre : List V) (left right : V) :
    runFrom (fileTime pre) (frame 72 left (fileCode pre right)) =
      frame 72 (reverseFile pre left) right := by
  induction pre generalizing left with
  | nil => simp [fileTime, fileCode, reverseFile]
  | cons value pre ih =>
    simp only [fileTime, fileCode, reverseFile]
    rw [runFrom_add, forward_inc, ih]

/-- Return across a fixed finite prefix from the literal separator entry48. -/
theorem return_inc_file (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 48 (reverseFile pre left) right) =
      leftFrame 48 left (fileCode pre right) := by
  induction pre generalizing left right with
  | nil => simp [fileTime, fileCode, reverseFile]
  | cons value pre ih =>
    simp only [fileTime, fileCode, reverseFile]
    rw [show (value+2+fileTime pre : V) = fileTime pre+(value+2) by ring,
      runFrom_add, ih, return_inc_probe]

/-- The added one is carried across a separator and the next unary block. -/
lemma shift_carry (value next left : V) :
    bitPrefix true (next+1) (4*bitPrefix true value left+2) =
      reverseBlock next (bitPrefix true (value+1) left) := by
  unfold reverseBlock
  congr 1
  rw [bitPrefix_succ]
  simp only [digit, if_true]
  ring

/-- External list induction only; every unary length and the spare count are
arbitrary internal values, handled by the previously checked scan theorems. -/
theorem shift_file_zero_spares (rest : List V) (value count left : V) :
    runFrom (value+fileTime rest+2*count+2)
        (frame 94 left (bitPrefix true value (fileCode rest (zeroBlocks count 0)))) =
      leftFrame 63
        (reverseZeroBlocks count (reverseFile rest (bitPrefix true (value+1) left))) 0 := by
  induction rest generalizing value left with
  | nil => simpa [fileTime, fileCode, reverseFile] using shift_zero_spares value count left
  | cons next rest ih =>
    have row : actionLookup (94 : V) (digit true) = 4*94+3+digit true :=
      right_row_of_nat true 94 (by decide)
    have block (right : V) : registerBlock next right = 4*bitPrefix true next right+2 := by
      unfold registerBlock
      rw [bitPrefix_succ]
      simp only [digit, if_true]
      ring
    simp only [fileTime, fileCode, reverseFile]
    rw [show (value+(next+2+fileTime rest)+2*count+2 : V) =
        value+(2+(next+fileTime rest+2*count+2)) by ring,
      runFrom_add, scan_right true 94 row, block, runFrom_add, shift_separator,
      ih next (4*bitPrefix true value left+2), shift_carry]

/-- Return through the variable zero tail, a fixed finite suffix, and the
nonempty target. The right tape is arbitrary throughout this return. -/
theorem return_file_zero_spares (rest : List V) (entry value count left right : V)
    (hentry : actionLookup entry (digit true) = 4*63+2) :
    runFrom (fileTime rest+value+2+2*count)
        (leftFrame entry
          (reverseZeroBlocks count (reverseFile rest (reverseBlock value left))) right) =
      leftFrame 48 left (registerBlock value (fileCode rest (zeroBlocks count right))) := by
  induction rest generalizing entry value left right with
  | nil => simpa [fileTime, fileCode, reverseFile] using
      return_zero_spares entry value count left right hentry
  | cons next rest ih =>
    have h48 : actionLookup (48 : V) (digit true) = 4*63+2 := by
      simpa only [digit, if_true, Nat.cast_ofNat,
        show (4*63+1+1 : V) = 4*63+2 by ring] using
        left_transition_of_nat (V := V) true true 48 63 (by decide)
    simp only [fileTime, fileCode, reverseFile]
    rw [show (next+2+fileTime rest+value+2+2*count : V) =
        (fileTime rest+next+2+2*count)+(value+2) by ring,
      runFrom_add, ih entry next (reverseBlock value left) right hentry]
    simpa using return_zero_spares 48 value (0 : V) left
      (registerBlock next (fileCode rest (zeroBlocks count right))) h48

/-- Exact increment endpoint with arbitrary internal following register values. -/
theorem increment_file_zero_spares (rest : List V) (value count left : V) :
    runFrom (2*value+2*fileTime rest+4*count+7)
        (frame 72 left (4*bitPrefix true value (fileCode rest (zeroBlocks count 0)))) =
      leftFrame 48 left (registerBlock (value+1) (fileCode rest (zeroBlocks count 0))) := by
  have h63 : actionLookup (63 : V) (digit true) = 4*63+2 := by
    simpa only [digit, if_true, Nat.cast_ofNat,
      show (4*63+1+1 : V) = 4*63+2 by ring] using
      left_transition_of_nat (V := V) true true 63 63 (by decide)
  rw [show (2*value+2*fileTime rest+4*count+7 : V) =
      2+((value+fileTime rest+2*count+2)+(fileTime rest+(value+1)+2+2*count)) by ring,
    runFrom_add, restore_mark, runFrom_add, shift_file_zero_spares, shifted_target_left]
  exact return_file_zero_spares rest 63 (value+1) count left 0 h63

/-- Complete marked-target increment endpoint, including seek and return over
the preceding fixed finite prefix. No first-exit assertion is needed here. -/
theorem increment_zip (pre rest : List V) (value count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime rest+4*count+7)
        (frame 72 left (fileCode pre
          (4*bitPrefix true value (fileCode rest (zeroBlocks count 0))))) =
      leftFrame 48 left (fileCode pre
        (registerBlock (value+1) (fileCode rest (zeroBlocks count 0)))) := by
  rw [show (2*fileTime pre+2*value+2*fileTime rest+4*count+7 : V) =
      fileTime pre+((2*value+2*fileTime rest+4*count+7)+fileTime pre) by ring,
    runFrom_add, forward_inc_file, runFrom_add, increment_file_zero_spares,
    return_inc_file]

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterFilePerm252
