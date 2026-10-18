import BusyBeaver.ZFC.ArithmeticControlAXACPush254

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
open ArithmeticControlRead254 (acReg)
open ArithmeticControlCopyBack254 (argumentPushFile)
open ArithmeticControlAXACPush254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254.copyEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254.exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254.acPushFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254.copy_tail_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254.ac_push_run

example : (source entry).2 = .decnz 1 := entry_source
example : (source copyEntry).2 = .decnz 3 := copyEntry_source
example : (source ArithmeticControlAXACPush254.exit).2 = .decnz 2 := exit_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (argumentPushFile acReg file) i = regValue file i := acPushFile_other file i ht hs

example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (argumentPushFile acReg file) s1Reg = 0 :=
  (acPushFile_other file s1Reg (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (argumentPushFile acReg file) s2Reg = 0 :=
  (acPushFile_other file s2Reg (by decide) (by decide)).trans h2

example (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file acReg + 2) (liveValue (number copyEntry : V) file) =
      liveValue (number ArithmeticControlAXACPush254.exit : V)
        (put twReg (regValue file twReg + regValue file acReg) file) := copy_tail_run file h1

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number ArithmeticControlAXACPush254.exit : V)
        (put twReg (regValue file acReg)
          (put wsReg (ArithmeticCantor.cantor (regValue file twReg) (regValue file wsReg)) file)) :=
  ac_push_run file h1 h2
