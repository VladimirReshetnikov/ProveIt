import BusyBeaver.ZFC.ArithmeticControlAXSecondImp254
import BusyBeaver.ZFC.ArithmeticControlAXNextImp254

set_option autoImplicit false
noncomputable section

/-!
Actual AX prefix41→354: retain the first two implications on the work stack
and construct wim(P1, AC). All register files and clocks are internal to IΣ₁.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (s1Reg plReg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXSecondImp254 ArithmeticControlAXNextImp254
open FiniteControlTable254

theorem second_third_join : ArithmeticControlAXConstructor254.exit =
    ArithmeticControlAXNextParamPush254.entry := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def axThirdImpFile (file : V) : V := nextImpFile (axSecondImpFile file)

theorem axThirdImpFile_tw (file : V) : regValue (axThirdImpFile file) twReg =
    wim (regValue file p1Reg) (regValue file acReg) := by
  rw [axThirdImpFile, nextImpFile_tw,
    axSecondImpFile_other file p1Reg (by decide) (by decide) (by decide) (by decide),
    axSecondImpFile_other file acReg (by decide) (by decide) (by decide) (by decide)]

theorem axThirdImpFile_ws (file : V) : regValue (axThirdImpFile file) wsReg =
    cantor
      (wim (wim (regValue file acReg) (first (second (regValue file plReg))))
        (regValue file p1Reg))
      (cantor (wal (regValue file p1Reg) (regValue file cacheReg))
        (cantor (regValue file twReg) (regValue file wsReg))) := by
  rw [axThirdImpFile, nextImpFile_ws, axSecondImpFile_tw, axSecondImpFile_ws]

theorem axThirdImpFile_cache (file : V) : regValue (axThirdImpFile file) cacheReg =
    regValue file cacheReg + first (regValue file plReg) := by
  rw [axThirdImpFile, nextImpFile_other _ cacheReg (by decide) (by decide),
    axSecondImpFile_cache]

theorem axThirdImpFile_pl (file : V) : regValue (axThirdImpFile file) plReg =
    second (second (regValue file plReg)) := by
  rw [axThirdImpFile, nextImpFile_other _ plReg (by decide) (by decide), axSecondImpFile_pl]

theorem axThirdImpFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (axThirdImpFile file) i = regValue file i := by
  rw [axThirdImpFile, nextImpFile_other _ i ht hs,
    axSecondImpFile_other file i ht hs hc hp]

theorem ax_third_imp_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlAXACConstructor254.exit : V) (axThirdImpFile file) := by
  have hf1 : regValue (axSecondImpFile file) s1Reg = 0 :=
    (axSecondImpFile_other file s1Reg (by decide) (by decide) (by decide) (by decide)).trans h1
  have hf2 : regValue (axSecondImpFile file) s2Reg = 0 :=
    (axSecondImpFile_other file s2Reg (by decide) (by decide) (by decide) (by decide)).trans h2
  obtain ⟨tf, htf, hf⟩ := ax_second_imp_run file h1 h2
  obtain ⟨ts, _, hs⟩ := next_imp_run (axSecondImpFile file) hf1 hf2
  rw [second_third_join] at hf
  refine ⟨tf + ts, le_trans htf (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hf]
  exact hs

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254
