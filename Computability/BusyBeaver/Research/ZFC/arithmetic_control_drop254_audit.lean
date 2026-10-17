import BusyBeaver.ZFC.ArithmeticControlDrop254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlDrop254 ArithmeticControlPair254
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.prefixTWInc_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.prefixWSTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.cacheCopyTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.cacheRestoreTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.dropReturn_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.next_drop_return
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.prefix_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.cache_restore_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.drop_return_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.drop_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254.dispatch_drop_run

example : source prefixWSTest=([true,true,true,false,true,false,true,false,true,false,false],.decnz 2) := prefixWSTest_source
example : source cacheCopyTest=([true,true,true,false,true,false,true,true,false,false],.decnz 5) := cacheCopyTest_source
example : source cacheRestoreTest=([true,true,true,false,true,false,true,true,true,false],.decnz 6) := cacheRestoreTest_source
example : source dropReturn=([true,true,true,false,true,true],.brk 1) := dropReturn_source
example : prefixTW.sourceIndex=twReg ∧ prefixTW.targetIndex=s1Reg := ⟨rfl,rfl⟩
example : prefixWS.sourceIndex=wsReg ∧ prefixWS.targetIndex=twReg := ⟨rfl,rfl⟩
example : pushWS.sourceIndex=s2Reg ∧ pushWS.targetIndex=wsReg := ⟨rfl,rfl⟩
example : cacheCopy.sourceIndex=cacheReg ∧ cacheCopy.firstIndex=twReg ∧ cacheCopy.secondIndex=s1Reg := ⟨rfl,rfl,rfl⟩
example : cacheRestore.sourceIndex=s1Reg ∧ cacheRestore.targetIndex=cacheReg := ⟨rfl,rfl⟩

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (file : V) (h1 : regValue file s1Reg=0) :
    controlRun ((3*regValue file twReg+1)+(3*regValue file wsReg+1))
      (liveValue (number dropEntry : V) file)=
      liveValue (number dropPairTest : V) (prefixFile file) := prefix_run file h1
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number dropEntry : V) file)=
        liveValue (number cacheCopyTest : V) (pushFile file) := push_run file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) :
    controlRun (7*regValue file cacheReg+2)
      (liveValue (number cacheCopyTest : V) file)=
      liveValue (number dropReturn : V)
        (put twReg (regValue file twReg+regValue file cacheReg) file) := cache_restore_run file h1
example (file : V) :
    controlRun 1 (liveValue (number dropReturn : V) file)=
      liveValue (number fetchTest : V) file := drop_return_run file
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number dropEntry : V) file)=
        liveValue (number fetchTest : V)
          (put twReg (regValue file cacheReg)
            (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)) := drop_run file h1 h2
example (file : V) (ha : regValue file acReg=1)
    (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number dispatchEntry : V) file)=
        liveValue (number fetchTest : V) (dropFile (put acReg 0 file)) := dispatch_drop_run file ha h1 h2
example (file : V) : regValue (dropFile file) twReg=regValue file cacheReg := by
  exact write_at _ _ _
example (file : V) :
    regValue (dropFile file) wsReg=cantor (regValue file twReg) (regValue file wsReg) := by
  unfold dropFile put
  rw [write_other _ _ twReg wsReg (by decide),write_at]
example (file : V) (q : Fin 9) (hqtw : twReg≠q) (hqws : wsReg≠q) :
    regValue (dropFile file) q=regValue file q := by
  unfold dropFile put
  rw [write_other _ _ twReg q hqtw,write_other _ _ wsReg q hqws]
end Model
