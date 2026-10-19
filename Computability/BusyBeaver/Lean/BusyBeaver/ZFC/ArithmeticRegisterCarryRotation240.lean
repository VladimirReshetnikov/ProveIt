import BusyBeaver.ZFC.ArithmeticMachineScansRotation240
import BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252

set_option autoImplicit false

/-!
Exact unary carry, seek, rollback and return endpoints for Rotation240.
Every register value and both complete numeric tape halves are arbitrary
elements of an IΣ1 model. Only the pure registerBlock/reverseBlock definitions
are reused from the older arithmetic forward module; every executed step and
scan is the checked Rotation240 run. The twelve row premises are discharged
against its one literal table. No whole-file, spare-count, first-exit or
dispatch simulation is asserted.

The carry/rollback contracts follow Rotation240Boxes and its Rotation244
predecessor; the return proof follows ArithmeticRegisterReturnPerm252.
Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252
open ArithmeticMachineGraphPerm252 (lookupNat)
open ArithmeticMachineGraphRotation240 ArithmeticMachineStepRotation240
open ArithmeticMachineRunFromRotation240
open ArithmeticRegisterForwardPerm252 (registerBlock reverseBlock)

abbrev carryState : Nat := (oldStateRotation240 95).val + 1
abbrev carryProbeState : Nat := (oldStateRotation240 109).val + 1
abbrev seekState : Nat := (oldStateRotation240 73).val + 1
abbrev seekProbeState : Nat := (oldStateRotation240 83).val + 1
abbrev rollbackState : Nat := (oldStateRotation240 112).val + 1
abbrev rollbackProbeState : Nat := (oldStateRotation240 131).val + 1
abbrev returnOnesState : Nat := (oldStateRotation240 63).val + 1
abbrev returnZeroState : Nat := (oldStateRotation240 48).val + 1

theorem state_codes :
    carryState = 1 ∧ carryProbeState = 97 ∧ seekState = 65 ∧ seekProbeState = 75 ∧
    rollbackState = 100 ∧ rollbackProbeState = 118 ∧
    returnOnesState = 55 ∧ returnZeroState = 41 := by decide +kernel

private theorem carry_zero : lookupNat literalRows 0 carryState 0 =
    4 * carryProbeState + 4 := by decide +kernel
private theorem carry_probe_one : lookupNat literalRows 0 carryProbeState 1 =
    4 * carryState + 3 := by decide +kernel
private theorem carry_one : lookupNat literalRows 0 carryState 1 =
    4 * carryState + 4 := by decide +kernel
private theorem seek_zero : lookupNat literalRows 0 seekState 0 =
    4 * seekProbeState + 3 := by decide +kernel
private theorem seek_probe_one : lookupNat literalRows 0 seekProbeState 1 =
    4 * seekState + 4 := by decide +kernel
private theorem seek_one : lookupNat literalRows 0 seekState 1 =
    4 * seekState + 4 := by decide +kernel
private theorem rollback_zero : lookupNat literalRows 0 rollbackState 0 =
    4 * rollbackProbeState + 2 := by decide +kernel
private theorem rollback_probe_one : lookupNat literalRows 0 rollbackProbeState 1 =
    4 * rollbackState + 1 := by decide +kernel
private theorem rollback_one : lookupNat literalRows 0 rollbackState 1 =
    4 * rollbackState + 2 := by decide +kernel
private theorem return_one : lookupNat literalRows 0 returnOnesState 1 =
    4 * returnOnesState + 2 := by decide +kernel
private theorem return_zero : lookupNat literalRows 0 returnOnesState 0 =
    4 * returnZeroState + 1 := by decide +kernel
private theorem return_probe_one : lookupNat literalRows 0 returnZeroState 1 =
    4 * returnOnesState + 2 := by decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Nearest-first left tape after replacing the leading 01 by 10. -/
noncomputable def carryReverseBlock (value left : V) : V :=
  bitPrefix true value (4 * left + 2)

theorem registerBlock_expanded (value suffix : V) :
    registerBlock value suffix = 4 * bitPrefix true value suffix + 2 := by
  unfold registerBlock
  rw [bitPrefix_succ]
  simp only [digit, if_true]
  ring

/-- A final carried one turns the prefix into an ordinary reversed block. -/
theorem carry_reverse_snoc (value left : V) :
    2 * carryReverseBlock value left + 1 = reverseBlock value (2 * left + 1) := by
  unfold carryReverseBlock reverseBlock
  rw [bitPrefix_succ]
  simp only [digit, if_true]
  rw [show (2 * (2 * left + 1) : V) = 4 * left + 2 by ring]

/-- Two actual right rows rewrite 01 to 10 and retain the entire suffix. -/
theorem carry_separator (left suffix : V) :
    runFrom 2 (frame (carryState : V) left (4 * suffix + 2)) =
      frame (carryState : V) (4 * left + 2) suffix := by
  conv_lhs => arg 1; rw [show (2 : V) = 1 + 1 by ring]
  rw [runFrom_first,
    show (4 * suffix + 2 : V) = 2 * (2 * suffix + digit true) + digit false by
      simp only [digit, if_true, Bool.false_eq_true, if_false]; ring,
    ArithmeticMachineScansRotation240.step_right_numeral false true
      carryState carryProbeState carry_zero,
    runFrom_one,
    ArithmeticMachineScansRotation240.step_right_numeral true false
      carryProbeState carryState carry_probe_one]
  simp only [digit, if_true, Bool.false_eq_true, if_false, add_zero]
  congr 1
  ring

/-- The carried unary block has its separator/header swapped, unlike seek. -/
theorem carry_block (value left suffix : V) :
    runFrom (value + 2) (frame (carryState : V) left (registerBlock value suffix)) =
      frame (carryState : V) (carryReverseBlock value left) suffix := by
  rw [show (value + 2 : V) = 2 + value by ring, registerBlock_expanded,
    runFrom_add, carry_separator,
    ArithmeticMachineScansRotation240.scan_right_numeral true true carryState carry_one]
  rfl

/-- The increment seeker crosses the same block without changing its bits. -/
theorem seek_block (value left suffix : V) :
    runFrom (value + 2) (frame (seekState : V) left (registerBlock value suffix)) =
      frame (seekState : V) (reverseBlock value left) suffix := by
  have first : stepValue (frame (seekState : V) left (registerBlock value suffix)) =
      frame (seekProbeState : V) (2 * left) (bitPrefix true (value + 1) suffix) := by
    simpa only [registerBlock, digit, Bool.false_eq_true, if_false, add_zero] using
      ArithmeticMachineScansRotation240.step_right_numeral false false
        seekState seekProbeState seek_zero left (bitPrefix true (value + 1) suffix)
  have second : stepValue
      (frame (seekProbeState : V) (2 * left) (bitPrefix true (value + 1) suffix)) =
      frame (seekState : V) (2 * (2 * left) + digit true) (bitPrefix true value suffix) := by
    rw [bitPrefix_succ,
      ArithmeticMachineScansRotation240.step_right_numeral true true
        seekProbeState seekState seek_probe_one]
  rw [show (value + 2 : V) = (value + 1) + 1 by ring,
    runFrom_first, first, runFrom_first, second,
    ArithmeticMachineScansRotation240.scan_right_numeral true true seekState seek_one,
    bitPrefix_push]
  rfl

/-- The left-moving inverse of the separator rewrite, with arbitrary right tape. -/
theorem rollback_pair (left right : V) :
    runFrom 2 (leftFrame (rollbackState : V) (4 * left + 2) right) =
      leftFrame (rollbackState : V) left (4 * right + 2) := by
  conv_lhs => arg 1; rw [show (2 : V) = 1 + 1 by ring]
  rw [runFrom_first,
    show (4 * left + 2 : V) = 2 * (2 * left + digit true) + digit false by
      simp only [digit, if_true, Bool.false_eq_true, if_false]; ring,
    ArithmeticMachineScansRotation240.step_left_recenter false true
      (rollbackState : V) (rollbackProbeState : V)
      (ArithmeticMachineScansRotation240.left_transition_of_nat false true
        rollbackState rollbackProbeState rollback_zero),
    runFrom_one,
    ArithmeticMachineScansRotation240.step_left_recenter true false
      (rollbackProbeState : V) (rollbackState : V)
      (ArithmeticMachineScansRotation240.left_transition_of_nat true false
        rollbackProbeState rollbackState rollback_probe_one)]
  simp only [digit, if_true, Bool.false_eq_true, if_false, add_zero]
  congr 1
  ring

/-- Restore one carried block, scanning its arbitrary internal number of ones. -/
theorem rollback_block (value left right : V) :
    runFrom (value + 2)
        (leftFrame (rollbackState : V) (carryReverseBlock value left) right) =
      leftFrame (rollbackState : V) left (registerBlock value right) := by
  unfold carryReverseBlock
  rw [runFrom_add,
    ArithmeticMachineScansRotation240.scan_left_numeral true true rollbackState rollback_one,
    rollback_pair, registerBlock_expanded]

/-- One entry row, value unchanged one-scans, then the zero separator.
The explicit entry premise allows both actual return states to share the proof. -/
theorem return_block (entry : V)
    (hentry : actionLookup entry (digit true) =
      4 * (returnOnesState : V) + 1 + digit true) (value left right : V) :
    runFrom (value + 2) (leftFrame entry (reverseBlock value left) right) =
      leftFrame (returnZeroState : V) left (registerBlock value right) := by
  have first : stepValue (leftFrame entry (reverseBlock value left) right) =
      leftFrame (returnOnesState : V) (bitPrefix true value (2 * left))
        (2 * right + digit true) := by
    unfold reverseBlock
    rw [bitPrefix_succ,
      ArithmeticMachineScansRotation240.step_left_recenter true true
        entry (returnOnesState : V) hentry]
  have last (tail : V) : stepValue (leftFrame (returnOnesState : V) (2 * left) tail) =
      leftFrame (returnZeroState : V) left (2 * tail) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero] using
      ArithmeticMachineScansRotation240.step_left_recenter false false
        (returnOnesState : V) (returnZeroState : V)
        (ArithmeticMachineScansRotation240.left_transition_of_nat false false
          returnOnesState returnZeroState return_zero) left tail
  rw [show (value + 2 : V) = (value + 1) + 1 by ring,
    runFrom_first, first, runFrom_add,
    ArithmeticMachineScansRotation240.scan_left_numeral true true returnOnesState return_one,
    runFrom_one, last, bitPrefix_push]
  rfl

theorem return_ones (value left right : V) :
    runFrom (value + 2)
        (leftFrame (returnOnesState : V) (reverseBlock value left) right) =
      leftFrame (returnZeroState : V) left (registerBlock value right) :=
  return_block (returnOnesState : V)
    (ArithmeticMachineScansRotation240.left_transition_of_nat true true
      returnOnesState returnOnesState return_one) value left right

theorem return_probe (value left right : V) :
    runFrom (value + 2)
        (leftFrame (returnZeroState : V) (reverseBlock value left) right) =
      leftFrame (returnZeroState : V) left (registerBlock value right) :=
  return_block (returnZeroState : V)
    (ArithmeticMachineScansRotation240.left_transition_of_nat true true
      returnZeroState returnOnesState return_probe_one) value left right

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240
