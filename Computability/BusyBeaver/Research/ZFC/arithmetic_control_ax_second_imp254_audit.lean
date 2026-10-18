import BusyBeaver.ZFC.ArithmeticControlAXSecondImp254

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
open ArithmeticControlAXSecondImp254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254.first_second_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254.axSecondImpFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254.axSecondImpFile_ws
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254.axSecondImpFile_cache
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254.axSecondImpFile_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254.axSecondImpFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXSecondImp254.ax_second_imp_run

example : ArithmeticControlConstructor254.impExit = ArithmeticControlAXParamPush254.entry :=
  first_second_join

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) : regValue (axSecondImpFile file) twReg =
    wim (wim (regValue file acReg) (first (second (regValue file plReg))))
      (regValue file p1Reg) := axSecondImpFile_tw file

example (file : V) : regValue (axSecondImpFile file) wsReg =
    cantor (wal (regValue file p1Reg) (regValue file cacheReg))
      (cantor (regValue file twReg) (regValue file wsReg)) := axSecondImpFile_ws file

example (file : V) : regValue (axSecondImpFile file) cacheReg =
    regValue file cacheReg + first (regValue file plReg) := axSecondImpFile_cache file

example (file : V) : regValue (axSecondImpFile file) plReg =
    second (second (regValue file plReg)) := axSecondImpFile_pl file

example (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (axSecondImpFile file) i = regValue file i := axSecondImpFile_other file i ht hs hc hp

example (file : V) : regValue (axSecondImpFile file) acReg = regValue file acReg :=
  axSecondImpFile_other file acReg (by decide) (by decide) (by decide) (by decide)

example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (axSecondImpFile file) s1Reg = 0 :=
  (axSecondImpFile_other file s1Reg (by decide) (by decide) (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (axSecondImpFile file) s2Reg = 0 :=
  (axSecondImpFile_other file s2Reg (by decide) (by decide) (by decide) (by decide)).trans h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlAXConstructor254.exit : V) (axSecondImpFile file) :=
  ax_second_imp_run file h1 h2
