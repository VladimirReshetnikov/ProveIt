import BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlParamPush254 (pushFile)
open ArithmeticControlCopyBack254 (argumentPushFile)
open ArithmeticControlAXArgumentPush254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254.argumentExit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254.exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254.argument_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254.plain_push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254.two_pushes_run

example : (source entry).2 = .decnz 1 := entry_source
example : (source argumentExit).2 = .decnz 1 := argumentExit_source
example : (source ArithmeticControlAXArgumentPush254.exit).2 = .decnz 8 := exit_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number argumentExit : V) (argumentPushFile acReg file) :=
  argument_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number argumentExit : V) file) =
      liveValue (number ArithmeticControlAXArgumentPush254.exit : V) (pushFile file) :=
  plain_push_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number ArithmeticControlAXArgumentPush254.exit : V)
        (pushFile (argumentPushFile acReg file)) :=
  two_pushes_run file h1 h2
