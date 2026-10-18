import BusyBeaver.ZFC.ArithmeticControlCopyBack254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlParamPush254 (PushShape)
open ArithmeticControlCopyBack254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCopyBack254.source_ne_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCopyBack254.source_ne_s1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCopyBack254.copy_back_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCopyBack254.argumentPushFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCopyBack254.argument_push_run

example (c : CopyBackShape) : c.copy.sourceIndex ≠ twReg := source_ne_tw c
example (c : CopyBackShape) : c.copy.sourceIndex ≠ s1Reg := source_ne_s1 c

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (c : CopyBackShape) (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file c.copy.sourceIndex + 2)
      (liveValue (number c.copy.test : V) file) =
      liveValue (number c.restore.exit : V)
        (put twReg (regValue file twReg + regValue file c.copy.sourceIndex) file) :=
  copy_back_run c file h1

example (c : CopyBackShape) (hc : c.copy.sourceIndex = acReg)
    (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file acReg + 2)
      (liveValue (number c.copy.test : V) file) =
      liveValue (number c.restore.exit : V)
        (put twReg (regValue file twReg + regValue file acReg) file) := by
  simpa only [hc] using copy_back_run c file h1

example (argument i : Fin 9) (file : V) (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (argumentPushFile argument file) i = regValue file i :=
  argumentPushFile_other argument i file ht hs

example (c : CopyBackShape) (file : V) (hw : c.copy.sourceIndex ≠ wsReg) :
    regValue (argumentPushFile c.copy.sourceIndex file) c.copy.sourceIndex =
      regValue file c.copy.sourceIndex :=
  argumentPushFile_other _ _ file (source_ne_tw c) hw

example (argument : Fin 9) (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (argumentPushFile argument file) s1Reg = 0 :=
  (argumentPushFile_other argument s1Reg file (by decide) (by decide)).trans h1

example (argument : Fin 9) (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (argumentPushFile argument file) s2Reg = 0 :=
  (argumentPushFile_other argument s2Reg file (by decide) (by decide)).trans h2

example (push : PushShape) (c : CopyBackShape)
    (join : push.output.exit = c.copy.test) (hw : c.copy.sourceIndex ≠ wsReg)
    (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number push.first.test : V) file) =
        liveValue (number c.restore.exit : V) (argumentPushFile c.copy.sourceIndex file) :=
  argument_push_run push c join hw file h1 h2
