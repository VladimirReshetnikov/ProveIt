import BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252
import BusyBeaver.ZFC.ArithmeticRegisterReturnPerm252

/-!
Increment's suffix shift through an arbitrary internal run of zero spares.
The final blank pair turns the actual machine back left. This is a numeric
endpoint for the changing tape, not a complete increment or dispatch theorem.
The shift_separator_steps and shift_suffix contracts originate in the
attributed RegisterIncrementPerm252 module and mira-emmy PR20 Box.v;
Mira-Cult, Jeff and Wade retain their attributions.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticZeroSpareScanPerm252
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
private instance leftFrame_delta : 𝚫₁-Function₃[V] leftFrame := by
  unfold leftFrame
  definability

/-- Actual numeric states94/108 swap separator01 to10 as they move right. -/
theorem shift_separator (left suffix : V) :
    runFrom 2 (frame 94 left (4*suffix+2)) =
      frame 94 (4*left+2) suffix := by
  have first : stepValue (frame 94 left (4*suffix+2)) =
      frame 108 (2*left+1) (2*suffix+1) := by
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero, Nat.cast_ofNat,
      show (2*(2*suffix+1) : V) = 4*suffix+2 by ring] using
      step_right_numeral false true 94 108 (by decide) left (2*suffix+1)
  have second : stepValue (frame 108 (2*left+1) (2*suffix+1)) =
      frame 94 (4*left+2) suffix := by
    simpa only [digit, Bool.false_eq_true, if_false, if_true, add_zero, Nat.cast_ofNat,
      show (2*(2*left+1) : V) = 4*left+2 by ring] using
      step_right_numeral true false 108 94 (by decide) (2*left+1) suffix
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second]

/-- On the blank exterior, write the added one and start the leftward return. -/
theorem shift_end (left : V) :
    runFrom 2 (frame 94 left 0) = leftFrame 63 (2*left+1) 0 := by
  have first : stepValue (frame 94 left 0) = frame 108 (2*left+1) 0 := by
    simpa [digit] using step_right_numeral false true 94 108 (by decide) left (0 : V)
  have second : stepValue (frame 108 (2*left+1) 0) = leftFrame 63 (2*left+1) 0 := by
    simpa [digit] using step_left_numeral false false 108 63 (by decide) (2*left+1) (0 : V)
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second]

def ZeroSpareShift (count : V) : Prop := ∀ value left : V,
  runFrom (value+2*count+2) (frame 94 left (bitPrefix true value (zeroBlocks count 0))) =
    leftFrame 63 (reverseZeroBlocks count (bitPrefix true (value+1) left)) 0
private instance zeroSpareShift_definable : 𝚷₁-Predicate (ZeroSpareShift (V := V)) := by
  unfold ZeroSpareShift
  definability

/-- All-internal suffix shift, including an empty spare tail and zero unary value. -/
theorem shift_zero_spares (value count left : V) :
    runFrom (value+2*count+2) (frame 94 left (bitPrefix true value (zeroBlocks count 0))) =
      leftFrame 63 (reverseZeroBlocks count (bitPrefix true (value+1) left)) 0 := by
  have row : actionLookup (94 : V) (digit true) = 4*94+3+digit true :=
    right_row_of_nat true 94 (by decide)
  have allCounts : ∀ count : V, ZeroSpareShift count := by
    intro count
    induction count using ISigma1.pi1_succ_induction
    · exact zeroSpareShift_definable
    case zero =>
      intro value left
      simp only [mul_zero, add_zero, zeroBlocks_zero, reverseZeroBlocks_zero]
      rw [runFrom_add, scan_right true 94 row, shift_end, bitPrefix_succ]
      rfl
    case succ count ih =>
      intro value left
      rw [show (value+2*(count+1)+2 : V) = value+(2+(0+2*count+2)) by ring,
        runFrom_add, scan_right true 94 row, zeroBlocks_succ, runFrom_add, shift_separator]
      have tail := ih (0 : V) (4*bitPrefix true value left+2)
      simp only [bitPrefix_zero] at tail
      rw [tail]
      have hleft : bitPrefix true (0+1) (4*bitPrefix true value left+2) =
          4*bitPrefix true (value+1) left+1 := by
        rw [bitPrefix_succ, bitPrefix_zero, bitPrefix_succ]
        simp only [digit, if_true]
        ring
      rw [hleft, reverseZeroBlocks_push]
  exact allCounts count value left

end SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252
