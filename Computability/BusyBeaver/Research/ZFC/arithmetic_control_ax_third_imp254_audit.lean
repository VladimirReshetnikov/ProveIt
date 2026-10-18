import BusyBeaver.ZFC.ArithmeticControlAXThirdImp254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (s1Reg plReg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXThirdImp254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254.second_third_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254.axThirdImpFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254.axThirdImpFile_ws
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254.axThirdImpFile_cache
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254.axThirdImpFile_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254.axThirdImpFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXThirdImp254.ax_third_imp_run

example : ArithmeticControlAXConstructor254.exit = ArithmeticControlAXNextParamPush254.entry :=
  second_third_join

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) : regValue (axThirdImpFile file) twReg =
    wim (regValue file p1Reg) (regValue file acReg) := axThirdImpFile_tw file

example (file : V) : regValue (axThirdImpFile file) wsReg =
    cantor
      (wim (wim (regValue file acReg) (first (second (regValue file plReg))))
        (regValue file p1Reg))
      (cantor (wal (regValue file p1Reg) (regValue file cacheReg))
        (cantor (regValue file twReg) (regValue file wsReg))) := axThirdImpFile_ws file

example (file : V) : regValue (axThirdImpFile file) cacheReg =
    regValue file cacheReg + first (regValue file plReg) := axThirdImpFile_cache file

example (file : V) : regValue (axThirdImpFile file) plReg =
    second (second (regValue file plReg)) := axThirdImpFile_pl file

example (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (axThirdImpFile file) i = regValue file i := axThirdImpFile_other file i ht hs hc hp

example (file : V) : regValue (axThirdImpFile file) acReg = regValue file acReg :=
  axThirdImpFile_other file acReg (by decide) (by decide) (by decide) (by decide)

example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (axThirdImpFile file) s1Reg = 0 :=
  (axThirdImpFile_other file s1Reg (by decide) (by decide) (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (axThirdImpFile file) s2Reg = 0 :=
  (axThirdImpFile_other file s2Reg (by decide) (by decide) (by decide) (by decide)).trans h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlAXACConstructor254.exit : V) (axThirdImpFile file) :=
  ax_third_imp_run file h1 h2
