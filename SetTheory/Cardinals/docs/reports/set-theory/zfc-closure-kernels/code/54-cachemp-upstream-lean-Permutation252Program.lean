import BusyBeaver.ZFC.Permutation252Frame
import BusyBeaver.ZFC.Bisim254
import BusyBeaver.ZFC.DirtyProgram254

/-!
The candidate frame's all-zero logical root has the actual literal register
program endpoint. This is separate from the generic frame definitions so
that binary-layout proofs do not depend on the 3,010-pair certificate check.
No binary instruction simulation or consistency calibration is inferred.
-/
namespace SetTheory.BusyBeaver.ZFC.Permutation252Program
open RegisterPath Permutation252Frame

private theorem enc_zero (i : Nat) :
    L2.enc ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ i = 0 := by
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i <;> rfl

/-- Arithmetic endpoint for the safe all-zero logical root. No model
completeness or consistency calibration is used by this composition. -/
theorem literal_zero_halts_iff_c254 :
    Halts Prog254.program zeroRoot ↔ Code254.C254 Code254.F := by
  have he : L2.enc ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ = zeroRoot.registers := funext enc_zero
  have h := (Bisim254.prog254_halts_iff (L2.enc ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩)).trans
    (DirtyProgram254.path_halts_iff _
      ⟨Code254.C254.truth, Code254.C254.truth, Enum254.good_zero⟩)
  simpa only [he, zeroRoot] using h

/-- The exact native-theory endpoint follows from the numerical adapter. -/
theorem literal_zero_halts_iff_native_refutation :
    Halts Prog254.program zeroRoot ↔ BProv NativeTheory254.NativeAx [] Form.fBot :=
  literal_zero_halts_iff_c254.trans NativeTheory254.c254_refutation_iff

end SetTheory.BusyBeaver.ZFC.Permutation252Program

