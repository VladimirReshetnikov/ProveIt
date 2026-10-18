import BusyBeaver.ZFC.ArithmeticControlAXNextImp254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlParamPush254 (paramPushFile)
open ArithmeticControlCopyBack254 (argumentPushFile)
open ArithmeticControlConstructor254 (constructorFile)
open ArithmeticControlAXNextImp254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.param_ac_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.ac_constructor_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.constructor_after_ac_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.ac_constructor_after_param_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.nextImpFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.nextImpFile_ws
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.nextImpFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.ac_constructor_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254.next_imp_run

example : ArithmeticControlAXNextParamPush254.exit = ArithmeticControlAXACPush254.entry :=
  param_ac_join

example : ArithmeticControlAXACPush254.exit = ArithmeticControlAXACConstructor254.entry :=
  ac_constructor_join

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) :
    constructorFile 0 (argumentPushFile acReg file) = acConstructorFile file :=
  constructor_after_ac_push file

example (file : V) : acConstructorFile (paramPushFile file) = nextImpFile file :=
  ac_constructor_after_param_push file

example (file : V) : regValue (nextImpFile file) twReg =
    wim (regValue file p1Reg) (regValue file acReg) := nextImpFile_tw file

example (file : V) : regValue (nextImpFile file) wsReg =
    cantor (regValue file twReg) (regValue file wsReg) := nextImpFile_ws file

example (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (nextImpFile file) i = regValue file i := nextImpFile_other file i ht hs

example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (nextImpFile file) s1Reg = 0 :=
  (nextImpFile_other file s1Reg (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (nextImpFile file) s2Reg = 0 :=
  (nextImpFile_other file s2Reg (by decide) (by decide)).trans h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXACPush254.entry : V) file) =
        liveValue (number ArithmeticControlAXACConstructor254.exit : V)
          (put twReg (wim (regValue file twReg) (regValue file acReg)) file) :=
  ac_constructor_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXNextParamPush254.entry : V) file) =
        liveValue (number ArithmeticControlAXACConstructor254.exit : V)
          (put twReg (wim (regValue file p1Reg) (regValue file acReg))
            (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)) :=
  next_imp_run file h1 h2
