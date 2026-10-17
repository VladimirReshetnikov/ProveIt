import BusyBeaver.ZFC.ArithmeticRegisterDecrementPerm252

/-!
The zero branch of marked-register decrement in the frozen252 machine.
The fixed finite prefix has arbitrary internal register values; both complete
tape halves are retained. Its register-file caller permits an arbitrary
internal zero-spare count and has the specified blank right exterior.
The construction follows the attributed RegisterBoxesPerm252 zero-box
contracts; Mira-Cult, Jeff and Wade retain their machine and framework credit.
No dispatcher refinement or consistency endpoint is asserted here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineStepPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticRegisterReturnPerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticZeroSpareScanPerm252 ArithmeticRegisterFilePerm252
open ArithmeticRegisterDecrementPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Literal states43/59/74/2 restore marked000 to010 in four moves. -/
theorem restore_zero (left right : V) :
    runFrom 4 (frame 43 left (8*right)) = frame 3 left (8*right+2) := by
  have first : stepValue (frame 43 left (8*right)) =
      frame 59 (2*left) (4*right) := by
    simpa [digit, Nat.cast_ofNat, show (2*(4*right) : V) = 8*right by ring] using
      step_right_numeral false false 43 59 (by decide) left (4*right)
  have second : stepValue (frame 59 (2*left) (4*right)) =
      frame 74 (4*left) (2*right) := by
    simpa [digit, Nat.cast_ofNat, show (2*(2*right) : V) = 4*right by ring,
      show (2*(2*left) : V) = 4*left by ring] using
      step_right_numeral false false 59 74 (by decide) (2*left) (2*right)
  have third : stepValue (frame 74 (4*left) (2*right)) =
      frame 2 (2*left) (4*right) := by
    have h := step_left_numeral false false 74 2 (by decide) (2*(2*left)) right
    rw [leftFrame_even] at h
    simpa [digit, Nat.cast_ofNat, leftFrame_even,
      show (2*(2*left) : V) = 4*left by ring,
      show (2*(2*right) : V) = 4*right by ring] using h
  have fourth : stepValue (frame 2 (2*left) (4*right)) =
      frame 3 left (8*right+2) := by
    have h := step_left_numeral false true 2 3 (by decide) (2*left) (2*right)
    simpa [digit, Nat.cast_ofNat, leftFrame_even,
      show (2*(2*right) : V) = 4*right by ring,
      show (2*(4*right+1) : V) = 8*right+2 by ring] using h
  conv_lhs => arg 1; rw [show (4 : V) = ((1+1)+1)+1 by ring]
  rw [runFrom_first, first, runFrom_first, second, runFrom_first, third,
    runFrom_one, fourth]

theorem return_dec_file (pre : List V) (left right : V) :
    runFrom (fileTime pre) (leftFrame 5 (reverseFile pre left) right) =
      leftFrame 5 left (fileCode pre right) := by
  induction pre generalizing left right with
  | nil => simp [fileTime, fileCode, reverseFile]
  | cons value pre ih =>
    simp only [fileTime, fileCode, reverseFile]
    rw [show (value+2+fileTime pre : V) = fileTime pre+(value+2) by ring,
      runFrom_add, ih, return_dec_probe]

/-- First step leaves the restored separator, then returns over every prefix block. -/
theorem return_zero_prefix (pre : List V) (left right : V) :
    runFrom (fileTime pre+1) (frame 3 (reverseFile pre left) (2*right)) =
      leftFrame 5 left (fileCode pre (2*right)) := by
  have step : stepValue (frame 3 (reverseFile pre left) (2*right)) =
      leftFrame 5 (reverseFile pre left) (2*right) := by
    simpa [digit, Nat.cast_ofNat] using
      step_left_numeral false false 3 5 (by decide) (reverseFile pre left) right
  rw [runFrom_first, step, return_dec_file]

/-- The suffix is arbitrary after its required leading zero. -/
theorem zero_box (pre : List V) (left right : V) :
    runFrom (2*fileTime pre+5) (frame 43 left (fileCode pre (8*right))) =
      leftFrame 5 left (fileCode pre (8*right+2)) := by
  rw [show (2*fileTime pre+5 : V) = fileTime pre+(4+(fileTime pre+1)) by ring,
    runFrom_add, forward_dec_file, runFrom_add, restore_zero]
  simpa only [show (2*(4*right+1) : V) = 8*right+2 by ring] using
    return_zero_prefix pre left (4*right+1)

lemma file_zero_tail_even (rest : List V) (count : V) :
    ∃ half : V, fileCode rest (zeroBlocks count 0) = 2*half := by
  cases rest with
  | nil => simpa [fileCode] using zeroBlocks_even count (0 : V)
  | cons value rest =>
    exact ⟨bitPrefix true (value+1) (fileCode rest (zeroBlocks count 0)), rfl⟩

/-- Zero decrement restores the target's header and preserves every register
and spare. The count and all fixed-prefix/suffix register values are internal. -/
theorem zero_decrement (pre rest : List V) (count left : V) :
    runFrom (2*fileTime pre+5)
        (frame 43 left (fileCode pre (4*fileCode rest (zeroBlocks count 0)))) =
      leftFrame 5 left
        (fileCode pre (registerBlock 0 (fileCode rest (zeroBlocks count 0)))) := by
  obtain ⟨half, hh⟩ := file_zero_tail_even rest count
  simpa only [hh, registerBlock_zero, show (4*(2*half) : V) = 8*half by ring] using
    zero_box pre left half

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterZeroPerm252
