import BusyBeaver.ZFC.ArithmeticControlAXFirstImp254
import BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254

set_option autoImplicit false
noncomputable section

/-!
Actual AX prefix41→275. The first implication prefix and the parameter
constructor compose at222. All files and positive clocks are internal to IΣ₁.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (s1Reg plReg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXFirstImp254 ArithmeticControlAXParamConstructor254
open FiniteControlTable254

theorem first_second_join : ArithmeticControlConstructor254.impExit =
    ArithmeticControlAXParamPush254.entry := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact complete-file result, with the temporary parameter push cancelled. -/
def axSecondImpFile (file : V) : V := axParamConstructorFile (axFirstImpFile file)

theorem axSecondImpFile_tw (file : V) : regValue (axSecondImpFile file) twReg =
    wim (wim (regValue file acReg) (first (second (regValue file plReg))))
      (regValue file p1Reg) := by
  rw [axSecondImpFile, axParamConstructorFile_tw, axFirstImpFile_tw,
    axFirstImpFile_other file p1Reg (by decide) (by decide) (by decide) (by decide)]

theorem axSecondImpFile_ws (file : V) : regValue (axSecondImpFile file) wsReg =
    cantor (wal (regValue file p1Reg) (regValue file cacheReg))
      (cantor (regValue file twReg) (regValue file wsReg)) := by
  rw [axSecondImpFile, axParamConstructorFile_other _ wsReg (by decide), axFirstImpFile_ws]

theorem axSecondImpFile_cache (file : V) : regValue (axSecondImpFile file) cacheReg =
    regValue file cacheReg + first (regValue file plReg) := by
  rw [axSecondImpFile, axParamConstructorFile_other _ cacheReg (by decide), axFirstImpFile_cache]

theorem axSecondImpFile_pl (file : V) : regValue (axSecondImpFile file) plReg =
    second (second (regValue file plReg)) := by
  rw [axSecondImpFile, axParamConstructorFile_other _ plReg (by decide), axFirstImpFile_pl]

theorem axSecondImpFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (axSecondImpFile file) i = regValue file i := by
  rw [axSecondImpFile, axParamConstructorFile_other _ i ht,
    axFirstImpFile_other file i ht hs hc hp]

/-- Actual AX41→275, with a positive internal clock and the entire output file. -/
theorem ax_second_imp_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlAXConstructor254.exit : V) (axSecondImpFile file) := by
  have hf1 : regValue (axFirstImpFile file) s1Reg = 0 :=
    (axFirstImpFile_other file s1Reg (by decide) (by decide) (by decide) (by decide)).trans h1
  have hf2 : regValue (axFirstImpFile file) s2Reg = 0 :=
    (axFirstImpFile_other file s2Reg (by decide) (by decide) (by decide) (by decide)).trans h2
  obtain ⟨tf, htf, hf⟩ := ax_first_imp_run file h1 h2
  obtain ⟨ts, _, hs⟩ := ax_param_constructor_run (axFirstImpFile file) hf1 hf2
  rw [first_second_join] at hf
  refine ⟨tf + ts, le_trans htf (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hf]
  exact hs

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254
