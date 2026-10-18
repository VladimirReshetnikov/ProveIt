import BusyBeaver.ZFC.ArithmeticControlAXParamPush254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlParamPush254 (paramPushFile)
open ArithmeticControlAXParamPush254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254.copyEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254.exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254.paramPushFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254.copy_tail_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254.ax_param_push_run

example : (source entry).2 = .decnz 1 := entry_source
example : (source copyEntry).2 = .decnz 4 := copyEntry_source
example : (source ArithmeticControlAXParamPush254.exit).2 = .decnz 2 := exit_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (paramPushFile file) i = regValue file i := paramPushFile_other file i ht hs

example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (paramPushFile file) s1Reg = 0 :=
  (paramPushFile_other file s1Reg (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (paramPushFile file) s2Reg = 0 :=
  (paramPushFile_other file s2Reg (by decide) (by decide)).trans h2

example (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file p1Reg + 2) (liveValue (number copyEntry : V) file) =
      liveValue (number ArithmeticControlAXParamPush254.exit : V)
        (put twReg (regValue file twReg + regValue file p1Reg) file) := copy_tail_run file h1

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number ArithmeticControlAXParamPush254.exit : V)
        (put twReg (regValue file p1Reg)
          (put wsReg (ArithmeticCantor.cantor (regValue file twReg) (regValue file wsReg)) file)) :=
  ax_param_push_run file h1 h2
