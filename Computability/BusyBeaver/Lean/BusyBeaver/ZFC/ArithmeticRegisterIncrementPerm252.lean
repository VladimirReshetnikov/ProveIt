import BusyBeaver.ZFC.ArithmeticZeroSpareShiftPerm252

/-!
Increment of one marked unary register followed by an arbitrary internal
number of zero spare registers. Complete tape halves are retained. This
endpoint does not yet permit a nonzero intervening/following register, assert
first exit, or establish a complete register-file/dispatch simulation.
The restore-mark, suffix-shift and return framework follows the attributed
RegisterIncrementPerm252 contracts and mira-emmy PR20 Box.v. Mira-Cult,
Jeff and Wade retain their machine, verification and framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticZeroSpareScanPerm252
open ArithmeticZeroSpareShiftPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance bitPrefix_delta (b : Bool) : 𝚫₁-Function₂[V] (bitPrefix b) :=
  (bitPrefix_defined b).graph_delta.to_definable
private instance zeroBlocks_delta : 𝚫₁-Function₂[V] zeroBlocks :=
  zeroBlocks_defined_delta.to_definable
private instance reverseZeroBlocks_delta : 𝚫₁-Function₂[V] reverseZeroBlocks :=
  reverseZeroBlocks_defined.graph_delta.to_definable
private instance registerBlock_delta : 𝚫₁-Function₂[V] registerBlock :=
  registerBlock_defined.graph_delta.to_definable
private instance reverseBlock_delta : 𝚫₁-Function₂[V] reverseBlock :=
  reverseBlock_defined.graph_delta.to_definable
private instance actionLookup_delta : 𝚫₁-Function₂[V] actionLookup :=
  actionLookup_defined.graph_delta.to_definable.of_zero
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom :=
  runFrom_defined_delta.to_definable
private instance frame_delta : 𝚫₁-Function₃[V] frame :=
  frame_defined.graph_delta.to_definable
private instance leftFrame_delta : 𝚫₁-Function₃[V] leftFrame := by
  unfold leftFrame
  definability

/-- Actual states72/82 restore the marked00 prefix to01 in two moves. -/
theorem restore_mark (left suffix : V) :
    runFrom 2 (frame 72 left (4*suffix)) = frame 94 (4*left+1) suffix := by
  have first : stepValue (frame 72 left (4*suffix)) =
      frame 82 (2*left) (2*suffix) := by
    simpa [digit, Nat.cast_ofNat, show (2*(2*suffix) : V) = 4*suffix by ring] using
      step_right_numeral false false 72 82 (by decide) left (2*suffix)
  have second : stepValue (frame 82 (2*left) (2*suffix)) =
      frame 94 (4*left+1) suffix := by
    simpa [digit, Nat.cast_ofNat, show (2*(2*left) : V) = 4*left by ring] using
      step_right_numeral false true 82 94 (by decide) (2*left) suffix
  conv_lhs => arg 1; rw [show (2 : V) = 1+1 by ring]
  rw [runFrom_first, first, runFrom_one, second]

def ReturnZeroSpares (count : V) : Prop := ∀ entry value left right : V,
  actionLookup entry (digit true) = 4*63+2 →
  runFrom (value+2+2*count)
      (leftFrame entry (reverseZeroBlocks count (reverseBlock value left)) right) =
    leftFrame 48 left (registerBlock value (zeroBlocks count right))
private instance returnZeroSpares_definable : 𝚷₁-Predicate (ReturnZeroSpares (V := V)) := by
  unfold ReturnZeroSpares
  definability

/-- Return over the zero spares and then the nonempty target register.
All four quantified arguments, including the entry state, are internal. -/
theorem return_zero_spares (entry value count left right : V)
    (hentry : actionLookup entry (digit true) = 4*63+2) :
    runFrom (value+2+2*count)
        (leftFrame entry (reverseZeroBlocks count (reverseBlock value left)) right) =
      leftFrame 48 left (registerBlock value (zeroBlocks count right)) := by
  have h63 : actionLookup (63 : V) (digit true) = 4*63+1+digit true :=
    left_transition_of_nat true true 63 63 (by decide)
  have hzero : actionLookup (63 : V) (digit false) = 4*48+1+digit false :=
    left_transition_of_nat false false 63 48 (by decide)
  have h48 : actionLookup (48 : V) (digit true) = 4*63+2 := by
    simpa [digit, Nat.cast_ofNat, add_assoc, show (1+1 : V) = 2 by ring] using
      left_transition_of_nat (V := V) true true 48 63 (by decide)
  have allCounts : ∀ count : V, ReturnZeroSpares count := by
    intro count
    induction count using ISigma1.pi1_succ_induction
    · exact returnZeroSpares_definable
    case zero =>
      intro entry value left right he
      simpa only [mul_zero, add_zero, reverseZeroBlocks_zero, zeroBlocks_zero]
        using return_block entry 63 48 (by simpa [digit, add_assoc, show (1+1 : V) = 2 by ring] using he)
          h63 hzero value left right
    case succ count ih =>
      intro entry value left right he
      have reverse : reverseZeroBlocks (count+1) (reverseBlock value left) =
          reverseBlock 0 (reverseZeroBlocks count (reverseBlock value left)) := by
        rw [reverseZeroBlocks_succ, reverseBlock_zero]
      have first : runFrom 2
          (leftFrame entry (reverseBlock 0 (reverseZeroBlocks count (reverseBlock value left))) right) =
          leftFrame 48 (reverseZeroBlocks count (reverseBlock value left)) (4*right+2) := by
        simpa only [zero_add, registerBlock_zero] using
          return_block entry 63 48 (by simpa [digit, add_assoc, show (1+1 : V) = 2 by ring] using he)
            h63 hzero (0 : V) (reverseZeroBlocks count (reverseBlock value left)) right
      rw [show (value+2+2*(count+1) : V) = 2+(value+2+2*count) by ring,
        reverse, runFrom_add, first, ih 48 value left (4*right+2) h48, zeroBlocks_push]
  exact allCounts count entry value left right hentry

/-- The suffix shift exits in the literal return entry63. -/
theorem return_zero_spares_inc_entry (value count left right : V) :
    runFrom (value+2+2*count)
        (leftFrame 63 (reverseZeroBlocks count (reverseBlock value left)) right) =
      leftFrame 48 left (registerBlock value (zeroBlocks count right)) :=
  return_zero_spares 63 value count left right (by
    simpa [digit, Nat.cast_ofNat, add_assoc, show (1+1 : V) = 2 by ring] using
      left_transition_of_nat (V := V) true true 63 63 (by decide))

lemma shifted_target_left (value left : V) :
    bitPrefix true (value+1) (4*left+1) = reverseBlock (value+1) left := by
  unfold reverseBlock
  simpa only [digit, if_true, show (2*(2*left)+1 : V) = 4*left+1 by ring] using
    bitPrefix_push true (value+1) (2*left)

/-- Full increment for a marked target immediately followed by zero spares. -/
theorem increment_last_zero_spares (value count left : V) :
    runFrom (2*value+4*count+7)
        (frame 72 left (4*bitPrefix true value (zeroBlocks count 0))) =
      leftFrame 48 left (registerBlock (value+1) (zeroBlocks count 0)) := by
  rw [show (2*value+4*count+7 : V) =
      2+((value+2*count+2)+((value+1)+2+2*count)) by ring,
    runFrom_add, restore_mark, runFrom_add, shift_zero_spares, shifted_target_left]
  exact return_zero_spares_inc_entry (value+1) count left 0

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterIncrementPerm252
