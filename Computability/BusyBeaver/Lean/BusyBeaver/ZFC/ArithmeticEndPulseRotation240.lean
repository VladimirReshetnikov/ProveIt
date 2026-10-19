import BusyBeaver.ZFC.ArithmeticRegisterCarryRotation240

set_option autoImplicit false

/-!
Literal Rotation240 mark restoration, end pulse and carry scan.
All numeric tape halves and scan lengths are arbitrary IΣ1 model elements.
The six-step end window assumes exactly four leading zero cells and retains
the arbitrary tape beyond them. Its blank specialization appends the block
011 and enters the literal return-zero state. No first-exit or dispatch claim.
The local contracts follow Rotation240Pulse/Rotation240Boxes; Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt retain their attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 (lookupNat)
open ArithmeticMachineGraphRotation240 ArithmeticMachineStepRotation240
open ArithmeticMachineRunFromRotation240 ArithmeticMachineUniformScansPerm252
open ArithmeticMachineScansRotation240 ArithmeticRegisterCarryRotation240

abbrev testState : Nat := (oldStateRotation240 75).val + 1
abbrev pulseState : Nat := (oldStateRotation240 255).val + 1

theorem pulse_state_codes : testState = 67 ∧ pulseState = 240 := by decide +kernel

private theorem seek_zero : lookupNat literalRows 0 seekState 0 =
    4*seekProbeState+3 := by decide +kernel
private theorem seek_probe_zero : lookupNat literalRows 0 seekProbeState 0 =
    4*carryState+4 := by decide +kernel
private theorem carry_zero : lookupNat literalRows 0 carryState 0 =
    4*carryProbeState+4 := by decide +kernel
private theorem carry_one : lookupNat literalRows 0 carryState 1 =
    4*carryState+4 := by decide +kernel
private theorem carry_probe_zero : lookupNat literalRows 0 carryProbeState 0 =
    4*testState+3 := by decide +kernel
private theorem test_zero : lookupNat literalRows 0 testState 0 =
    4*pulseState+4 := by decide +kernel
private theorem pulse_zero : lookupNat literalRows 0 pulseState 0 =
    4*pulseState+2 := by decide +kernel
private theorem pulse_one : lookupNat literalRows 0 pulseState 1 =
    4*rollbackProbeState+2 := by decide +kernel
private theorem rollback_probe_zero : lookupNat literalRows 0 rollbackProbeState 0 =
    4*returnZeroState+1 := by decide +kernel
private theorem rollback_probe_one : lookupNat literalRows 0 rollbackProbeState 1 =
    4*rollbackState+1 := by decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem restore_mark (left suffix : V) :
    runFrom 2 (frame (seekState : V) left (4*suffix)) =
      frame (carryState : V) (4*left+1) suffix := by
  have first : stepValue (frame (seekState : V) left (4*suffix)) =
      frame (seekProbeState : V) (2*left) (2*suffix) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*suffix) : V) = 4*suffix by ring] using
      step_right_numeral false false seekState seekProbeState seek_zero left (2*suffix)
  have second : stepValue (frame (seekProbeState : V) (2*left) (2*suffix)) =
      frame (carryState : V) (4*left+1) suffix := by
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero,
      show (2*(2*left)+1 : V) = 4*left+1 by ring] using
      step_right_numeral false true seekProbeState carryState seek_probe_zero (2*left) suffix
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second]

theorem pulse_zero_zero (left suffix : V) :
    runFrom 3 (frame (testState : V) left (4*suffix)) =
      leftFrame (rollbackProbeState : V) left (4*suffix+3) := by
  have first : stepValue (frame (testState : V) left (4*suffix)) =
      frame (pulseState : V) (2*left+1) (2*suffix) := by
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero,
      show (2*(2*suffix) : V) = 4*suffix by ring] using
      step_right_numeral false true testState pulseState test_zero left (2*suffix)
  have second : stepValue (frame (pulseState : V) (2*left+1) (2*suffix)) =
      leftFrame (pulseState : V) (2*left+1) (2*suffix+1) := by
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero] using
      step_left_numeral false true pulseState pulseState pulse_zero (2*left+1) suffix
  have third : stepValue (leftFrame (pulseState : V) (2*left+1) (2*suffix+1)) =
      leftFrame (rollbackProbeState : V) left (4*suffix+3) := by
    simpa only [digit, if_true,
      show (2*(2*suffix+1)+1 : V) = 4*suffix+3 by ring] using
      step_left_recenter true true (pulseState : V) (rollbackProbeState : V)
        (left_transition_of_nat true true pulseState rollbackProbeState pulse_one)
        left (2*suffix+1)
  conv_lhs => arg 1; rw [show (3 : V) = (1+1)+1 by ring]
  rw [runFrom_first, first, runFrom_first, second, runFrom_one, third]

theorem pulse_zero_one (left suffix : V) :
    runFrom 3 (frame (testState : V) left (4*suffix+2)) =
      leftFrame (rollbackState : V) left (4*suffix+2) := by
  have first : stepValue (frame (testState : V) left (4*suffix+2)) =
      frame (pulseState : V) (2*left+1) (2*suffix+1) := by
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero,
      show (2*(2*suffix+1) : V) = 4*suffix+2 by ring] using
      step_right_numeral false true testState pulseState test_zero left (2*suffix+1)
  have second : stepValue (frame (pulseState : V) (2*left+1) (2*suffix+1)) =
      leftFrame (rollbackProbeState : V) (2*left+1) (2*suffix+1) := by
    simpa only [digit, if_true] using
      step_left_numeral true true pulseState rollbackProbeState pulse_one (2*left+1) suffix
  have third : stepValue
        (leftFrame (rollbackProbeState : V) (2*left+1) (2*suffix+1)) =
      leftFrame (rollbackState : V) left (4*suffix+2) := by
    simpa only [digit, if_true, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*suffix+1) : V) = 4*suffix+2 by ring] using
      step_left_recenter true false (rollbackProbeState : V) (rollbackState : V)
        (left_transition_of_nat true false rollbackProbeState rollbackState rollback_probe_one)
        left (2*suffix+1)
  conv_lhs => arg 1; rw [show (3 : V) = (1+1)+1 by ring]
  rw [runFrom_first, first, runFrom_first, second, runFrom_one, third]

theorem carry_to_test (left suffix : V) :
    runFrom 2 (frame (carryState : V) left (4*suffix)) =
      frame (testState : V) (4*left+2) suffix := by
  have first : stepValue (frame (carryState : V) left (4*suffix)) =
      frame (carryProbeState : V) (2*left+1) (2*suffix) := by
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero,
      show (2*(2*suffix) : V) = 4*suffix by ring] using
      step_right_numeral false true carryState carryProbeState carry_zero left (2*suffix)
  have second : stepValue (frame (carryProbeState : V) (2*left+1) (2*suffix)) =
      frame (testState : V) (4*left+2) suffix := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*left+1) : V) = 4*left+2 by ring] using
      step_right_numeral false false carryProbeState testState carry_probe_zero (2*left+1) suffix
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second]

/-- Four zero cells suffice; all later cells are retained without a blank-tail premise. -/
theorem carry_end_window (left suffix : V) :
    runFrom 6 (frame (carryState : V) left (16*suffix)) =
      leftFrame (returnZeroState : V) (2*left+1) (8*suffix+6) := by
  have last : stepValue
        (leftFrame (rollbackProbeState : V) (4*left+2) (4*suffix+3)) =
      leftFrame (returnZeroState : V) (2*left+1) (8*suffix+6) := by
    simpa only [digit, Bool.false_eq_true, if_false, add_zero,
      show (2*(2*left+1) : V) = 4*left+2 by ring,
      show (2*(4*suffix+3) : V) = 8*suffix+6 by ring] using
      step_left_recenter false false (rollbackProbeState : V) (returnZeroState : V)
        (left_transition_of_nat false false rollbackProbeState returnZeroState rollback_probe_zero)
        (2*left+1) (4*suffix+3)
  conv_lhs => arg 1; rw [show (6 : V) = 2+(3+1) by ring]
  rw [show (16*suffix : V) = 4*(4*suffix) by ring,
    runFrom_add, carry_to_test, runFrom_add, pulse_zero_zero, runFrom_one, last]

theorem carry_end (left : V) :
    runFrom 6 (frame (carryState : V) left 0) =
      leftFrame (returnZeroState : V) (2*left+1) 6 := by
  simpa only [mul_zero, zero_add] using carry_end_window left (0 : V)

theorem carry_ones (length left right : V) :
    runFrom length (frame (carryState : V) left (bitPrefix true length right)) =
      frame (carryState : V) (bitPrefix true length left) right :=
  scan_right_numeral true true carryState carry_one length left right

end SetTheory.BusyBeaver.ZFC.ArithmeticEndPulseRotation240
