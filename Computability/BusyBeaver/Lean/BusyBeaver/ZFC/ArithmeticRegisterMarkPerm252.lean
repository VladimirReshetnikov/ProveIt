import BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252

/-!
Mark a selected primary register of the actual frozen252 arithmetic machine.
The selector and prefix length are externally bounded by nine; every register
value and both complete tape halves are arbitrary IΣ1 model elements.
The target's unary header is erased and every other bit is retained.

The skip/mark/return contracts follow RegisterMarkPerm252 and mira-emmy PR20
head 0d544f2a2e3c18f12278441a74b7879f31cbe856, ZF/m253/coq/tm/Box.v.
Mira-Cult, Jeff and Wade retain their machine and framework attributions.
Numeric working-state codes equal canonical table indices plus one.
No first-exit, absolute head, dispatcher/PC or PA endpoint is asserted.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticRegisterFilePerm252
open ArithmeticRegisterDecrementPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Arithmetic state codes of the nine physical selector states. -/
def skipCode : Nat → Nat
  | 0 => 60
  | 1 => 44
  | 2 => 31
  | 3 => 56
  | 4 => 38
  | 5 => 40
  | 6 => 28
  | 7 => 1
  | _ => 68

private theorem skip_one_facts : ∀ j : Fin 9,
    lookupNat literalRows 0 (skipCode j.val) 1 = 4*skipCode j.val+4 := by decide
private theorem skip_next_facts : ∀ j : Fin 8,
    lookupNat literalRows 0 (skipCode (j.val+1)) 0 = 4*skipCode j.val+3 := by decide

/-- Each of the nine literal selector states scans unary ones unchanged. -/
theorem skip_one (j : Nat) (hj : j < 9) :
    actionLookup (skipCode j : V) (digit true) = 4*(skipCode j : V)+3+digit true := by
  apply right_row_of_nat true (skipCode j)
  simpa only [Bool.toNat_true, Nat.add_assoc] using skip_one_facts ⟨j,hj⟩

/-- The zero separator decrements the external physical selector index. -/
theorem skip_next (j : Nat) (hj : j < 8) :
    actionLookup (skipCode (j+1) : V) (digit false) =
      4*(skipCode j : V)+3+digit false := by
  apply right_transition_of_nat false false (skipCode (j+1)) (skipCode j)
  simpa only [Bool.toNat_false, Nat.add_zero] using skip_next_facts ⟨j,hj⟩

/-- One block is crossed while the finite selector index decreases by one. -/
theorem skip_block (j : Nat) (hj : j < 8) (value left right : V) :
    runFrom (value+2) (frame (skipCode (j+1) : V) left (registerBlock value right)) =
      frame (skipCode j : V) (reverseBlock value left) right := by
  have first : stepValue
      (frame (skipCode (j+1) : V) left (registerBlock value right)) =
        frame (skipCode j : V) (2*left) (bitPrefix true (value+1) right) := by
    simpa only [registerBlock, digit, Bool.false_eq_true, if_false, add_zero] using
      step_right_row false false (skipCode (j+1) : V) (skipCode j : V)
        (skip_next j hj) left (bitPrefix true (value+1) right)
  rw [show (value+2 : V) = (value+1)+1 by ring,
    runFrom_first, first, scan_right true (skipCode j : V) (skip_one j (by omega))]
  rfl

/-- Seek a selected register through an externally fixed prefix of length≤8. -/
theorem skip_file (pre : List V) (hp : pre.length < 9) (left right : V) :
    runFrom (fileTime pre)
        (frame (skipCode pre.length : V) left (fileCode pre right)) =
      frame 60 (reverseFile pre left) right := by
  induction pre generalizing left with
  | nil => simp [fileTime, fileCode, reverseFile, skipCode, Nat.cast_ofNat]
  | cons value pre ih =>
    have hj : pre.length < 8 := by
      simp only [List.length_cons] at hp
      omega
    have hpre : pre.length < 9 := by omega
    simp only [fileTime, fileCode, reverseFile, List.length_cons]
    rw [runFrom_add, skip_block pre.length hj, ih hpre]

/-- Three literal transitions erase exactly the selected register's header.
No validity or shape restriction on the remaining right half is needed. -/
theorem mark_steps (value left right : V) :
    runFrom 3 (frame 60 left (registerBlock value right)) =
      leftFrame 4 left (4*bitPrefix true value right) := by
  have first : stepValue (frame 60 left (registerBlock value right)) =
      frame 2 (2*left) (bitPrefix true (value+1) right) := by
    simpa [registerBlock, digit, Nat.cast_ofNat] using
      step_right_numeral false false 60 2 (by decide) left
        (bitPrefix true (value+1) right)
  have second : stepValue (frame 2 (2*left) (bitPrefix true (value+1) right)) =
      frame 4 left (4*bitPrefix true value right) := by
    rw [bitPrefix_succ]
    have h := step_left_numeral true false 2 4 (by decide) (2*left)
      (bitPrefix true value right)
    rw [leftFrame_even] at h
    simpa [digit, Nat.cast_ofNat,
      show (2*(2*bitPrefix true value right) : V) = 4*bitPrefix true value right by ring] using h
  have third : stepValue (frame 4 left (4*bitPrefix true value right)) =
      leftFrame 4 left (4*bitPrefix true value right) := by
    simpa [digit, Nat.cast_ofNat,
      show (2*(2*bitPrefix true value right) : V) = 4*bitPrefix true value right by ring] using
      step_left_numeral false false 4 4 (by decide) left (2*bitPrefix true value right)
  conv_lhs => arg 1; rw [show (3 : V) = (1+1)+1 by ring]
  rw [runFrom_first, first, runFrom_first, second, runFrom_one, third]

/-- Generic actual-lookup entry into the mark return family. Only the fixed
finite list is externally iterated; value and both complete halves are internal. -/
theorem return_mark_target (rest : List V) (entry value left right : V)
    (hentry : actionLookup entry (digit true) = 4*6+2) :
    runFrom (fileTime rest+value+2)
        (leftFrame entry (reverseFile rest (reverseBlock value left)) right) =
      leftFrame 7 left (registerBlock value (fileCode rest right)) := by
  induction rest generalizing entry value left right with
  | nil =>
    have h6 : actionLookup (6 : V) (digit true) = 4*6+1+digit true :=
      left_transition_of_nat true true 6 6 (by decide)
    have hzero : actionLookup (6 : V) (digit false) = 4*7+1+digit false :=
      left_transition_of_nat false false 6 7 (by decide)
    simpa only [fileTime, fileCode, reverseFile, zero_add] using
      return_block entry 6 7
        (by simpa [digit, add_assoc, show (1+1 : V) = 2 by ring] using hentry)
        h6 hzero value left right
  | cons next rest ih =>
    have h7 : actionLookup (7 : V) (digit true) = 4*6+2 := by
      simpa [digit, Nat.cast_ofNat, add_assoc, show (1+1 : V) = 2 by ring] using
        left_transition_of_nat (V := V) true true 7 6 (by decide)
    simp only [fileTime, fileCode, reverseFile]
    rw [show (next+2+fileTime rest+value+2 : V) =
        (fileTime rest+next+2)+(value+2) by ring,
      runFrom_add, ih entry next (reverseBlock value left) right hentry]
    simpa using return_block 7 6 7
      (by simpa [digit, add_assoc, show (1+1 : V) = 2 by ring] using h7)
      (left_transition_of_nat true true 6 6 (by decide))
      (left_transition_of_nat false false 6 7 (by decide))
      value left (registerBlock next (fileCode rest right))

def markExit : List V → V
  | [] => 4
  | _ :: _ => 7

/-- Return over a nonempty prefix, or retain entry4 for an empty prefix. -/
theorem return_mark_prefix (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 4 (reverseFile pre left) right) =
      leftFrame (markExit pre) left (fileCode pre right) := by
  cases pre with
  | nil => simp [fileTime, reverseFile, fileCode, markExit]
  | cons value pre =>
    have h4 : actionLookup (4 : V) (digit true) = 4*6+2 := by
      simpa [digit, Nat.cast_ofNat, add_assoc, show (1+1 : V) = 2 by ring] using
        left_transition_of_nat (V := V) true true 4 6 (by decide)
    simpa only [fileTime, reverseFile, fileCode, markExit,
      show (value+2+fileTime pre : V) = fileTime pre+value+2 by ring] using
      return_mark_target pre (4 : V) value left right h4

/-- Complete numeric marking box, with arbitrary entire tape context.
The prefix length is externally bounded; its entries and target are internal. -/
theorem mark_file (pre : List V) (hp : pre.length < 9) (value left right : V) :
    runFrom (2*fileTime pre+3)
        (frame (skipCode pre.length : V) left (fileCode pre (registerBlock value right))) =
      leftFrame (markExit pre) left (fileCode pre (4*bitPrefix true value right)) := by
  rw [show (2*fileTime pre+3 : V) = fileTime pre+(3+fileTime pre) by ring,
    runFrom_add, skip_file pre hp, runFrom_add, mark_steps, return_mark_prefix]

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252
