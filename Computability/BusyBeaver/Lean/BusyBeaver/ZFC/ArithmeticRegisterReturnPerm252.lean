import BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252

/-!
Return across an arbitrary internal unary register in the actual frozen252
arithmetic evaluator. The complete left and right tape halves are retained.
These are exact recentered endpoints; the whole register-file invariant and
the internal binary/scheduler comparison remain separate obligations.

The return scanner follows RegisterMarkPerm252.return_end_left and the
return rows in RegisterBoxesPerm252 and RegisterIncrementPerm252, attributed
to mira-emmy PR20 head 0d544f2a2e3c18f12278441a74b7879f31cbe856,
ZF/m253/coq/tm/Box.v. Mira-Cult, Jeff and Wade retain their machine,
verification and framework attributions.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A left-moving row includes its write and move, also for target zero. -/
lemma step_left_row (read write : Bool) (q target : V)
    (hrow : actionLookup q (digit read) = 4*target+1+digit write) (left suffix : V) :
    stepValue (frame q left (2*suffix+digit read)) =
      leftFrame target left (2*suffix+digit write) := by
  have hn : 4*target+1+digit (V := V) write ≠ 0 := by
    rw [show (4*target+1+digit write : V) = (4*target+digit write)+1 by ring]
    simp
  unfold frame
  change genericStepValue actionLookup (cantor q (cantor left (2*suffix+digit read))) = _
  simp only [genericStepValue, first_cantor, second_cantor, digit_mod_two, hrow, if_neg hn]
  rw [apply_left, digit_div_two]
  unfold leftFrame
  congr 2
  ring

/-- Recenter the input from its nearest left cell before taking a row. -/
lemma step_left_recenter (read write : Bool) (q target : V)
    (hrow : actionLookup q (digit read) = 4*target+1+digit write) (left right : V) :
    stepValue (leftFrame q (2*left+digit read) right) =
      leftFrame target left (2*right+digit write) := by
  have he : leftFrame q (2*left+digit read) right =
      frame q left (2*right+digit read) := by
    unfold leftFrame
    rw [digit_div_two, digit_mod_two]
    congr 1
    ring
  rw [he, step_left_row read write q target hrow]

lemma left_transition_of_nat (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+1+write.toNat) :
    actionLookup (q : V) (digit read) = 4*(target : V)+1+digit write := by
  have h := actionLookup_numeral (V := V) q read.toNat
  rw [hrow] at h
  cases read <;> cases write <;> simpa [digit, numeral_eq_natCast] using h

lemma step_left_numeral (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+1+write.toNat) (left suffix : V) :
    stepValue (frame (q : V) left (2*suffix+digit read)) =
      leftFrame (target : V) left (2*suffix+digit write) :=
  step_left_row read write (q : V) (target : V)
    (left_transition_of_nat read write q target hrow) left suffix

/-- One entry row, value self-loops, then the zero separator.
The entry state can be the probe of the preceding block. -/
theorem return_block (entry ones exitState : V)
    (hentry : actionLookup entry (digit true) = 4*ones+1+digit true)
    (hones : actionLookup ones (digit true) = 4*ones+1+digit true)
    (hzero : actionLookup ones (digit false) = 4*exitState+1+digit false)
    (value left right : V) :
    runFrom (value+2) (leftFrame entry (reverseBlock value left) right) =
      leftFrame exitState left (registerBlock value right) := by
  have first : stepValue (leftFrame entry (reverseBlock value left) right) =
      leftFrame ones (bitPrefix true value (2*left)) (2*right+digit true) := by
    unfold reverseBlock
    rw [bitPrefix_succ, step_left_recenter true true entry ones hentry]
  have last (tail : V) : stepValue (leftFrame ones (2*left) tail) =
      leftFrame exitState left (2*tail) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero] using
      step_left_recenter false false ones exitState hzero left tail
  rw [show (value+2 : V) = (value+1)+1 by ring, runFrom_first, first,
    runFrom_add, scan_left true ones hones, runFrom_one, last, bitPrefix_push]
  rfl

/-- The zero-decrement return family, starting in its one state. -/
theorem return_dec (value left right : V) :
    runFrom (value+2) (leftFrame 3 (reverseBlock value left) right) =
      leftFrame 5 left (registerBlock value right) :=
  return_block 3 3 5
    (left_transition_of_nat true true 3 3 (by decide))
    (left_transition_of_nat true true 3 3 (by decide))
    (left_transition_of_nat false false 3 5 (by decide)) value left right

/-- The same family accepts the probe state between successive blocks. -/
theorem return_dec_probe (value left right : V) :
    runFrom (value+2) (leftFrame 5 (reverseBlock value left) right) =
      leftFrame 5 left (registerBlock value right) :=
  return_block 5 3 5
    (left_transition_of_nat true true 5 3 (by decide))
    (left_transition_of_nat true true 3 3 (by decide))
    (left_transition_of_nat false false 3 5 (by decide)) value left right

theorem return_mark (value left right : V) :
    runFrom (value+2) (leftFrame 4 (reverseBlock value left) right) =
      leftFrame 7 left (registerBlock value right) :=
  return_block 4 6 7
    (left_transition_of_nat true true 4 6 (by decide))
    (left_transition_of_nat true true 6 6 (by decide))
    (left_transition_of_nat false false 6 7 (by decide)) value left right

theorem return_mark_probe (value left right : V) :
    runFrom (value+2) (leftFrame 7 (reverseBlock value left) right) =
      leftFrame 7 left (registerBlock value right) :=
  return_block 7 6 7
    (left_transition_of_nat true true 7 6 (by decide))
    (left_transition_of_nat true true 6 6 (by decide))
    (left_transition_of_nat false false 6 7 (by decide)) value left right

theorem return_inc (value left right : V) :
    runFrom (value+2) (leftFrame 63 (reverseBlock value left) right) =
      leftFrame 48 left (registerBlock value right) :=
  return_block 63 63 48
    (left_transition_of_nat true true 63 63 (by decide))
    (left_transition_of_nat true true 63 63 (by decide))
    (left_transition_of_nat false false 63 48 (by decide)) value left right

theorem return_inc_probe (value left right : V) :
    runFrom (value+2) (leftFrame 48 (reverseBlock value left) right) =
      leftFrame 48 left (registerBlock value right) :=
  return_block 48 63 48
    (left_transition_of_nat true true 48 63 (by decide))
    (left_transition_of_nat true true 63 63 (by decide))
    (left_transition_of_nat false false 63 48 (by decide)) value left right

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252
