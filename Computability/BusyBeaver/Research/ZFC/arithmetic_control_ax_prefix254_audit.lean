import BusyBeaver.ZFC.ArithmeticControlAXPrefix254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry dispatchEntry)
open ArithmeticControlAXPrefix254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.nextPush_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.parameterCopy_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.ax_push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.ax_parameter_copy_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.ax_prefix_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254.dispatch_ax_prefix_run

example : (source axEntry).2 = .decnz 1 := congrArg Prod.snd entry_source
example : (source nextPush).2 = .decnz 1 := congrArg Prod.snd nextPush_source
example : (source parameterCopy).2 = .decnz 4 := parameterCopy_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number parameterCopy : V) (pushFile file) := ax_push_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file p1Reg + 2) (liveValue (number parameterCopy : V) file) =
      liveValue (number nextPush : V)
        (put twReg (regValue file twReg + regValue file p1Reg) file) :=
  ax_parameter_copy_run file h1

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number nextPush : V) (paramPushFile file) := ax_prefix_run file h1 h2

example (file c : V) (ha : regValue file acReg = c + 3)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number dispatchEntry : V) file) =
      liveValue (number nextPush : V) (paramPushFile (put acReg c file)) :=
  dispatch_ax_prefix_run file c ha h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number nextPush : V)
        (put twReg (regValue file p1Reg)
          (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)) :=
  ax_prefix_run file h1 h2
