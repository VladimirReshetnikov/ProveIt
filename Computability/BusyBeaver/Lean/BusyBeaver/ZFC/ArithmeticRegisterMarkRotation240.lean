import BusyBeaver.ZFC.ArithmeticIncrementRotation240
import BusyBeaver.ZFC.RegisterMarkRotation240

set_option autoImplicit false

/-!
Selected-register marking for the exact Rotation240 arithmetic run. The
physical selector is externally bounded by nine; register values, spare count
and both complete tape halves are arbitrary elements of an IΣ1 model.
Only the selected 01 header becomes 00, and the excursion ends one cell left
of its original origin. No first-exit or complete dispatch theorem is asserted.

The finite-prefix proof follows ArithmeticRegisterMarkPerm252, but every row,
scan and run below uses Rotation240. State codes are tied to its checked
RegisterMarkRotation240 interface. Mira-Cult, Jeff Ketchersid, Andrew James
Wade and ProveIt retain the machine and framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252
open ArithmeticMachineGraphPerm252 (lookupNat)
open ArithmeticMachineGraphRotation240 ArithmeticMachineStepRotation240
open ArithmeticMachineRunFromRotation240 ArithmeticMachineScansRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)
open ArithmeticOneRegisterBlocksRotation240 ArithmeticCarryTraversalRotation240
open ArithmeticIncrementRotation240 (reverseFile)

/-- Numeric codes use the actual external selector, in physical-register order. -/
def skipCode (j : Nat) : Nat := (RegisterMarkRotation240.skip j).val + 1
abbrev restoreCode : Nat := RegisterMarkRotation240.restoreZero.val + 1
abbrev markFirstCode : Nat := RegisterMarkRotation240.markFirst.val + 1
abbrev markOnesCode : Nat := RegisterMarkRotation240.markReturnOnes.val + 1
abbrev markZeroCode : Nat := RegisterMarkRotation240.markReturnZero.val + 1

theorem state_codes :
    (List.range 9).map skipCode = [52,37,26,49,33,34,23,56,61] ∧
    restoreCode = 17 ∧ markFirstCode = 2 ∧ markOnesCode = 3 ∧ markZeroCode = 4 := by
  decide +kernel

theorem skip_state_code (j : Nat) :
    ArithmeticMachinePerm252.stateCode (some (RegisterMarkRotation240.skip j)) =
      skipCode j := rfl

private theorem skip_one_facts : ∀ j : Fin 9,
    lookupNat literalRows 0 (skipCode j.val) 1 = 4*skipCode j.val+4 := by decide +kernel
private theorem skip_next_facts : ∀ j : Fin 8,
    lookupNat literalRows 0 (skipCode (j.val+1)) 0 = 4*skipCode j.val+3 := by decide +kernel
private theorem skip_target : lookupNat literalRows 0 (skipCode 0) 0 =
    4*restoreCode+3 := by decide +kernel
private theorem erase_one : lookupNat literalRows 0 restoreCode 1 =
    4*markFirstCode+1 := by decide +kernel
private theorem mark_back : lookupNat literalRows 0 markFirstCode 0 =
    4*markFirstCode+1 := by decide +kernel
private theorem mark_enter : lookupNat literalRows 0 markFirstCode 1 =
    4*markOnesCode+2 := by decide +kernel
private theorem mark_return_one : lookupNat literalRows 0 markOnesCode 1 =
    4*markOnesCode+2 := by decide +kernel
private theorem mark_return_zero : lookupNat literalRows 0 markOnesCode 0 =
    4*markZeroCode+1 := by decide +kernel
private theorem mark_return_probe : lookupNat literalRows 0 markZeroCode 1 =
    4*markOnesCode+2 := by decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Each actual selector scans arbitrary internal runs of unary ones unchanged. -/
theorem skip_one (j : Nat) (hj : j < 9) :
    actionLookup (skipCode j : V) (digit true) = 4*(skipCode j : V)+3+digit true := by
  apply right_transition_of_nat true true (skipCode j) (skipCode j)
  simpa only [Bool.toNat_true, Nat.add_assoc] using skip_one_facts ⟨j,hj⟩

theorem skip_next (j : Nat) (hj : j < 8) :
    actionLookup (skipCode (j+1) : V) (digit false) =
      4*(skipCode j : V)+3+digit false := by
  apply right_transition_of_nat false false (skipCode (j+1)) (skipCode j)
  simpa only [Bool.toNat_false, Nat.add_zero] using skip_next_facts ⟨j,hj⟩

/-- Cross one unchanged block while decreasing the finite selector index. -/
theorem skip_block (j : Nat) (hj : j < 8) (value left right : V) :
    runFrom (value+2) (frame (skipCode (j+1) : V) left (registerBlock value right)) =
      frame (skipCode j : V) (reverseBlock value left) right := by
  have first : stepValue
      (frame (skipCode (j+1) : V) left (registerBlock value right)) =
        frame (skipCode j : V) (2*left) (bitPrefix true (value+1) right) := by
    simpa only [registerBlock, digit, Bool.false_eq_true, if_false, add_zero] using
      step_right_row false false (skipCode (j+1) : V) (skipCode j : V)
        (skip_next j hj) left (bitPrefix true (value+1) right)
  conv_lhs => arg 1; rw [show (value+2 : V) = (value+1)+1 by ring]
  rw [runFrom_first, first,
    scan_right true true (skipCode j : V) (skip_one j (by omega))]
  rfl

/-- Seek through a finite physical prefix whose values may be nonstandard. -/
theorem skip_file (pre : List V) (hp : pre.length < 9) (left right : V) :
    runFrom (fileClock pre)
        (frame (skipCode pre.length : V) left (fileTape pre right)) =
      frame (skipCode 0 : V) (reverseFile pre left) right := by
  induction pre generalizing left with
  | nil => simp only [fileClock, fileTape, reverseFile, List.length_nil, runFrom_zero]
  | cons value pre ih =>
    have hj : pre.length < 8 := by
      simp only [List.length_cons] at hp
      omega
    have hpre : pre.length < 9 := by omega
    simp only [fileClock, fileTape, reverseFile, List.length_cons]
    rw [runFrom_add, skip_block pre.length hj, ih hpre]

private theorem leftFrame_even (state left right : V) :
    leftFrame state (2*left) right = frame state left (2*right) := by
  unfold leftFrame
  rw [even_div_two, even_mod_two, zero_add]

/-- Erase exactly the selected header in three steps, retaining the entire suffix. -/
theorem mark_steps (value left right : V) :
    runFrom 3 (frame (skipCode 0 : V) left (registerBlock value right)) =
      leftFrame (markFirstCode : V) left (4*bitPrefix true value right) := by
  have first : stepValue (frame (skipCode 0 : V) left (registerBlock value right)) =
      frame (restoreCode : V) (2*left) (bitPrefix true (value+1) right) := by
    simpa only [registerBlock, digit, Bool.false_eq_true, if_false, add_zero] using
      step_right_numeral false false (skipCode 0) restoreCode skip_target left
        (bitPrefix true (value+1) right)
  have second : stepValue
      (frame (restoreCode : V) (2*left) (bitPrefix true (value+1) right)) =
      frame (markFirstCode : V) left (4*bitPrefix true value right) := by
    rw [bitPrefix_succ]
    have h := step_left_numeral true false restoreCode markFirstCode erase_one
      (2*left) (bitPrefix true value right)
    rw [leftFrame_even] at h
    simpa only [digit, if_true, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*bitPrefix true value right) : V) = 4*bitPrefix true value right by ring] using h
  have third : stepValue (frame (markFirstCode : V) left (4*bitPrefix true value right)) =
      leftFrame (markFirstCode : V) left (4*bitPrefix true value right) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*bitPrefix true value right) : V) = 4*bitPrefix true value right by ring] using
      step_left_numeral false false markFirstCode markFirstCode mark_back left
        (2*bitPrefix true value right)
  conv_lhs => arg 1; rw [show (3 : V) = (1+1)+1 by ring]
  rw [runFrom_first, first, runFrom_first, second, runFrom_one, third]

/-- The mark-return family uses its own exact rows, distinct from carry return. -/
theorem return_mark_block (entry : V)
    (hentry : actionLookup entry (digit true) = 4*(markOnesCode : V)+1+digit true)
    (value left right : V) :
    runFrom (value+2) (leftFrame entry (reverseBlock value left) right) =
      leftFrame (markZeroCode : V) left (registerBlock value right) := by
  have first : stepValue (leftFrame entry (reverseBlock value left) right) =
      leftFrame (markOnesCode : V) (bitPrefix true value (2*left))
        (2*right+digit true) := by
    unfold reverseBlock
    rw [bitPrefix_succ,
      step_left_recenter true true entry (markOnesCode : V) hentry]
  have last (tail : V) : stepValue (leftFrame (markOnesCode : V) (2*left) tail) =
      leftFrame (markZeroCode : V) left (2*tail) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero] using
      step_left_recenter false false (markOnesCode : V) (markZeroCode : V)
        (left_transition_of_nat false false markOnesCode markZeroCode mark_return_zero) left tail
  conv_lhs => arg 1; rw [show (value+2 : V) = (value+1)+1 by ring]
  rw [runFrom_first, first, runFrom_add,
    scan_left_numeral true true markOnesCode mark_return_one,
    runFrom_one, last, bitPrefix_push]
  rfl

/-- Return across a fixed prefix, without restricting any internal value or tail. -/
theorem return_mark_target (rest : List V) (entry value left right : V)
    (hentry : actionLookup entry (digit true) = 4*(markOnesCode : V)+1+digit true) :
    runFrom (fileClock rest+value+2)
        (leftFrame entry (reverseFile rest (reverseBlock value left)) right) =
      leftFrame (markZeroCode : V) left (registerBlock value (fileTape rest right)) := by
  induction rest generalizing entry value left right with
  | nil =>
    simpa only [fileClock, fileTape, reverseFile, zero_add] using
      return_mark_block entry hentry value left right
  | cons next rest ih =>
    simp only [fileClock, fileTape, reverseFile]
    conv_lhs => arg 1; rw [show (next+2+fileClock rest+value+2 : V) =
      (fileClock rest+next+2)+(value+2) by ring]
    rw [runFrom_add, ih entry next (reverseBlock value left) right hentry]
    exact return_mark_block (markZeroCode : V)
      (left_transition_of_nat true true markZeroCode markOnesCode mark_return_probe)
      value left (registerBlock next (fileTape rest right))

/-- Empty prefixes exit at the first marker state; nonempty prefixes at its probe. -/
def markExitCode : List V → Nat
  | [] => markFirstCode
  | _ :: _ => markZeroCode

theorem return_mark_prefix (pre : List V) (left right : V) :
    runFrom (fileClock pre) (leftFrame (markFirstCode : V) (reverseFile pre left) right) =
      leftFrame (markExitCode pre : V) left (fileTape pre right) := by
  cases pre with
  | nil => simp only [fileClock, reverseFile, fileTape, markExitCode, runFrom_zero]
  | cons value pre =>
    simpa only [fileClock, reverseFile, fileTape, markExitCode,
      show (value+2+fileClock pre : V) = fileClock pre+value+2 by ring] using
      return_mark_target pre (markFirstCode : V) value left right
        (left_transition_of_nat true true markFirstCode markOnesCode mark_enter)

/-- Complete selected-register marking; the two full tape contexts are arbitrary. -/
theorem mark_file (pre : List V) (hp : pre.length < 9) (value left right : V) :
    runFrom (2*fileClock pre+3)
        (frame (skipCode pre.length : V) left (fileTape pre (registerBlock value right))) =
      leftFrame (markExitCode pre : V) left (fileTape pre (4*bitPrefix true value right)) := by
  conv_lhs => arg 1; rw [show (2*fileClock pre+3 : V) = fileClock pre+(3+fileClock pre) by ring]
  rw [runFrom_add, skip_file pre hp, runFrom_add, mark_steps, return_mark_prefix]

/-- Internal value-one spares are retained with an arbitrary complete right exterior. -/
theorem mark_file_spares (pre rest : List V) (hp : pre.length < 9)
    (value count left right : V) :
    runFrom (2*fileClock pre+3)
        (frame (skipCode pre.length : V) left
          (fileTape pre (registerBlock value (fileTape rest (oneBlocks count right))))) =
      leftFrame (markExitCode pre : V) left
        (fileTape pre (4*bitPrefix true value (fileTape rest (oneBlocks count right)))) :=
  mark_file pre hp value left (fileTape rest (oneBlocks count right))

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The symbolic selector's physical position determines the same exit state. -/
theorem markExitCode_split (pre : List V) (r : Fin 9) (hr : pre.length = r.val) :
    markExitCode pre = if r.val = 0 then markFirstCode else markZeroCode := by
  rw [←hr]
  cases pre <;> simp only [markExitCode, List.length_nil, List.length_cons,
    Nat.succ_ne_zero, if_true, if_false]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem markExit_state_code (pre : List V) :
    ArithmeticMachinePerm252.stateCode (some
      (if pre.length = 0 then RegisterMarkRotation240.markFirst
       else RegisterMarkRotation240.markReturnZero)) = markExitCode pre := by
  cases pre <;> simp only [List.length_nil, List.length_cons, Nat.succ_ne_zero,
    if_true, if_false, markExitCode, ArithmeticMachinePerm252.stateCode,
    markFirstCode, markZeroCode]

theorem mark_clock_positive (pre : List V) : 0 < 2*fileClock pre+3 := by
  rw [show (2*fileClock pre+3 : V) = (2*fileClock pre+2)+1 by ring]
  simp

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkRotation240
