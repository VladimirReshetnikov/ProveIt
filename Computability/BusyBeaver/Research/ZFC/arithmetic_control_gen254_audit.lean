import BusyBeaver.ZFC.ArithmeticControlGEN254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlPair254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXPrefix254 (nextPush)
open ArithmeticControlAXCachePush254 (cachePop)
open ArithmeticControlGEN254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.pairEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.nextRead_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.gen_tag_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.gen_pair_scale_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.genFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.gen_constructor_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.gen_cache_push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254.ax_gen_run

example : (source cachePop).2 = .decnz 2 := entry_source
example : (source pairEntry).2 = .decnz 1 := pairEntry_source
example : (source nextRead).2 = .decnz 8 := nextRead_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) :
    controlRun 2 (liveValue (number tagEntry : V) file) =
      liveValue (number nextRead : V) (put twReg (regValue file twReg + 2) file) :=
  gen_tag_run file

example (file : V) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number pairEntry : V) file) =
      liveValue (number nextRead : V)
        (put twReg (wal (regValue file s1Reg) (regValue file twReg)) (put s1Reg 0 file)) :=
  gen_pair_scale_run file h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number cachePop : V) file) =
      liveValue (number nextRead : V) (genFile file) := gen_constructor_run file h1 h2

example (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (genFile file) i = regValue file i := genFile_other file i ht hs

example (file : V) : regValue (genFile file) cacheReg = regValue file cacheReg :=
  genFile_other file cacheReg (by decide) (by decide)

example (file : V) : regValue (genFile file) plReg = regValue file plReg :=
  genFile_other file plReg (by decide) (by decide)

example (file : V) : regValue (genFile file) s1Reg = regValue file s1Reg :=
  genFile_other file s1Reg (by decide) (by decide)

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number nextPush : V) file) =
      liveValue (number nextRead : V) (cacheGenFile file) := gen_cache_push_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number nextRead : V) (axGenFile file) := ax_gen_run file h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number nextRead : V)
        (put twReg (wal (regValue file p1Reg) (regValue file cacheReg))
          (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)) :=
  ax_gen_run file h1 h2
