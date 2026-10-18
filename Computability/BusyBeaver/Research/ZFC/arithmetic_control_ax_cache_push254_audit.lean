import BusyBeaver.ZFC.ArithmeticControlAXCachePush254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXPrefix254 (nextPush)
open ArithmeticControlAXCachePush254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.cacheCopy_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.cachePop_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.ax_stack_push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.ax_cache_copy_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.cachePushFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.ax_cache_push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254.ax_two_parameters_run

example : (source nextPush).2 = .decnz 1 := congrArg Prod.snd entry_source
example : (source cacheCopy).2 = .decnz 5 := cacheCopy_source
example : (source cachePop).2 = .decnz 2 := congrArg Prod.snd cachePop_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number nextPush : V) file) =
      liveValue (number cacheCopy : V) (pushFile file) := ax_stack_push_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file cacheReg + 2)
      (liveValue (number cacheCopy : V) file) =
      liveValue (number cachePop : V)
        (put twReg (regValue file twReg + regValue file cacheReg) file) :=
  ax_cache_copy_run file h1

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number nextPush : V) file) =
      liveValue (number cachePop : V) (cachePushFile file) := ax_cache_push_run file h1 h2

example (file : V) : regValue (cachePushFile file) cacheReg = regValue file cacheReg :=
  cachePushFile_other file cacheReg (by decide) (by decide)

example (file : V) : regValue (cachePushFile file) p1Reg = regValue file p1Reg :=
  cachePushFile_other file p1Reg (by decide) (by decide)

example (file : V) : regValue (cachePushFile file) plReg = regValue file plReg :=
  cachePushFile_other file plReg (by decide) (by decide)

example (file : V) (p : Fin 9) (ht : p ≠ twReg) (hs : p ≠ wsReg) :
    regValue (cachePushFile file) p = regValue file p := cachePushFile_other file p ht hs

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number cachePop : V) (twoParametersFile file) := ax_two_parameters_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number cachePop : V)
        (put twReg (regValue file cacheReg)
          (put wsReg (cantor (regValue file p1Reg)
            (cantor (regValue file twReg) (regValue file wsReg))) file)) :=
  ax_two_parameters_run file h1 h2
