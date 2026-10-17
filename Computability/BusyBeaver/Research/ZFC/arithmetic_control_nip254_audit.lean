import BusyBeaver.ZFC.ArithmeticControlNip254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlNip254 ArithmeticControlDispatch254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (acReg)
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.cacheZeroS1_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.cacheZeroInc_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.cacheClearTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.cacheClearAgain_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.cacheClearExit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.stackPopEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.next_cache_zero_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.cache_clear_repeat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.nip_prepare
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.clear_cache
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.nip_cache_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.nip_cache_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.nip_nonfalsity
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254.dispatch_nip_nonfalsity

example : source cacheZeroS1=([true,true,true,false,true,false,false,true,false,true,true,false,false,false,true,true,false,false],.decnz 6) := cacheZeroS1_source
example : source cacheZeroInc=([true,true,true,false,true,false,false,true,false,true,true,false,false,false,true,true,true],.inc 5) := cacheZeroInc_source
example : source cacheClearTest=([true,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,false],.decnz 5) := cacheClearTest_source
example : source cacheClearAgain=([true,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true],.cont 1) := cacheClearAgain_source
example : source cacheClearExit=([true,true,true,false,true,false,false,true,false,true,true,false,false,true,true,true],.brk 1) := cacheClearExit_source
example : source stackPopEntry=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,false],.decnz 2) := stackPopEntry_source
example : resolveControl (incPath (source cacheZeroInc).1)=nipZeroH := next_cache_zero_inc
example : resolveControl (continuePath 1 (source cacheClearAgain).1)=cacheClearTest := cache_clear_repeat

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (file : V) (hs : regValue file s1Reg=0) :
    controlRun 2 (liveValue (number nipEntry : V) file)=
      liveValue (number nipTestH : V) file := nip_prepare file hs
example (file : V) :
    controlRun (2*regValue file cacheReg+1) (liveValue (number cacheClearTest : V) file)=
      liveValue (number cacheClearExit : V) (put cacheReg 0 file) := clear_cache file
example (file : V) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=0) :
    controlRun 8 (liveValue (number nipEntry : V) file)=
      liveValue (number stackPopEntry : V) file := nip_cache_zero file hs hh
example (file c : V) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=c+2) :
    controlRun (2*c+8) (liveValue (number nipEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 file) := nip_cache_positive file c hs hh
example (file : V) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg≠1) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number nipEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 file) := nip_nonfalsity file hs hh
example (file : V) (ha : regValue file acReg=2)
    (hs : regValue file s1Reg=0) (hh : regValue file cacheReg≠1) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dispatchEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 (put acReg 0 file)) :=
  dispatch_nip_nonfalsity file ha hs hh
example (r : Fin 9 → V) (hs : r s1Reg=0) (hh : r cacheReg≠1) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number nipEntry : V) (fileValue r))=
      liveValue (number stackPopEntry : V) (put cacheReg 0 (fileValue r)) := by
  apply nip_nonfalsity
  · simpa only [reg_file] using hs
  · simpa only [reg_file] using hh
example (file : V) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number nipEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 file) := by
  apply nip_nonfalsity file hs
  rw [hh]
  exact Ne.symm Arithmetic.one_ne_zero
example (file : V) (ha : regValue file acReg=2)
    (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=0) :
    controlRun 11 (liveValue (number dispatchEntry : V) file)=
      liveValue (number stackPopEntry : V) (put acReg 0 file) := by
  have hs' : regValue (put acReg 0 file) s1Reg=0 := by
    rw [put,write_other file 0 acReg s1Reg (by decide)]
    exact hs
  have hh' : regValue (put acReg 0 file) cacheReg=0 := by
    rw [put,write_other file 0 acReg cacheReg (by decide)]
    exact hh
  rw [show (11 : V)=3+8 by ring,controlRun_add,dispatch_nip file ha,
    nip_cache_zero (put acReg 0 file) hs' hh']
example (file c : V) (ha : regValue file acReg=2)
    (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=c+2) :
    controlRun (2*c+11) (liveValue (number dispatchEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 (put acReg 0 file)) := by
  have hs' : regValue (put acReg 0 file) s1Reg=0 := by
    rw [put,write_other file 0 acReg s1Reg (by decide)]
    exact hs
  have hh' : regValue (put acReg 0 file) cacheReg=c+2 := by
    rw [put,write_other file 0 acReg cacheReg (by decide)]
    exact hh
  rw [show 2*c+11=3+(2*c+8) by ring,controlRun_add,dispatch_nip file ha,
    nip_cache_positive (put acReg 0 file) c hs' hh']
end Model
