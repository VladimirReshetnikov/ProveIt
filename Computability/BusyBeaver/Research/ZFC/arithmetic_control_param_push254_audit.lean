import BusyBeaver.ZFC.ArithmeticControlParamPush254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlParamPush254
open ArithmeticControlPair254 (twReg)
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (mpEntry cacheReg)
open ArithmeticControlCompare254 (successEntry compareEntry compareFile)
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.param_copy_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.param_push_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.mpPopEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.mpParamCopyTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.successPairTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.successPairExit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.successParamCopyTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.successParamRestoreTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.mpParam_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.successParam_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254.mp_compare_tail_run

example : (source mpPopEntry).2=.decnz 2 := congrArg Prod.snd mpPopEntry_source
example : (source mpParamCopyTest).2=.decnz 4 := congrArg Prod.snd mpParamCopyTest_source
example : (source successPairTest).2=.decnz 1 := congrArg Prod.snd successPairTest_source
example : (source successPairExit).2=.decnz 7 := congrArg Prod.snd successPairExit_source
example : (source successParamCopyTest).2=.decnz 4 := congrArg Prod.snd successParamCopyTest_source
example : mpParam.copy.sourceIndex=p1Reg ∧ mpParam.copy.firstIndex=twReg := ⟨rfl,rfl⟩
example : successParam.restore.sourceIndex=s1Reg ∧ successParam.restore.targetIndex=p1Reg := ⟨rfl,rfl⟩

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (c : PushShape) (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.first.test : V) file)=
      liveValue (number c.output.exit : V) (pushFile file) := push_run c file h1 h2
example (c : ParamPushShape) (file : V) (h1 : regValue file s1Reg=0) :
    controlRun (7*regValue file p1Reg+2) (liveValue (number c.copy.test : V) file)=
      liveValue (number c.restore.exit : V)
        (put twReg (regValue file twReg+regValue file p1Reg) file) := param_copy_run c file h1
example (c : ParamPushShape) (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.push.first.test : V) file)=
      liveValue (number c.restore.exit : V) (paramPushFile file) := param_push_run c file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number mpPopEntry : V) (paramPushFile file) := mpParam_run file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number successEntry : V) file)=
      liveValue (number fetchTest : V) (paramPushFile file) := successParam_run file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) :
    controlRun (7*regValue file p1Reg+2) (liveValue (number mpParamCopyTest : V) file)=
      liveValue (number mpPopEntry : V)
        (put twReg (regValue file twReg+regValue file p1Reg) file) := by
  simpa only [mpParam,mpParamCopy,mpParamRestore] using param_copy_run mpParam file h1
example (file : V) (h1 : regValue file s1Reg=0) :
    controlRun (7*regValue file p1Reg+2) (liveValue (number successParamCopyTest : V) file)=
      liveValue (number fetchTest : V)
        (put twReg (regValue file twReg+regValue file p1Reg) file) := by
  simpa only [successParam,successParamCopy,successParamRestore] using param_copy_run successParam file h1
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (htw : regValue file twReg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number successEntry : V) file)=
      liveValue (number fetchTest : V)
        (put twReg (regValue file p1Reg) (put wsReg (cantor 0 (regValue file wsReg)) file)) := by
  simpa only [paramPushFile,htw] using successParam_run file h1 h2
example (file : V) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number compareEntry : V) file)=
      if regValue file s1Reg=regValue file cacheReg then
        liveValue (number fetchTest : V) (paramPushFile (compareFile file 0 0))
      else liveValue (number fetchTest : V) (compareFile file 0 0) := mp_compare_tail_run file h2
example (file : V) (h2 : regValue file s2Reg=0) (he : regValue file s1Reg=regValue file cacheReg) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number compareEntry : V) file)=
      liveValue (number fetchTest : V) (paramPushFile (compareFile file 0 0)) := by
  simpa only [if_pos he] using mp_compare_tail_run file h2
example (file : V) (h2 : regValue file s2Reg=0) (he : regValue file s1Reg≠regValue file cacheReg) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number compareEntry : V) file)=
      liveValue (number fetchTest : V) (compareFile file 0 0) := by
  simpa only [if_neg he] using mp_compare_tail_run file h2
example (file : V) (q : Fin 9) (hqt : twReg≠q) (hqw : wsReg≠q) :
    regValue (paramPushFile file) q=regValue file q := by
  unfold paramPushFile put
  rw [write_other _ _ twReg q hqt,write_other _ _ wsReg q hqw]
example (file : V) : regValue (paramPushFile file) p1Reg=regValue file p1Reg := by
  unfold paramPushFile put
  rw [write_other _ _ twReg p1Reg (by decide),write_other _ _ wsReg p1Reg (by decide)]
example (file : V) : regValue (paramPushFile file) twReg=regValue file p1Reg := by
  exact write_at _ _ _
example (file : V) :
    regValue (paramPushFile file) wsReg=cantor (regValue file twReg) (regValue file wsReg) := by
  unfold paramPushFile put
  rw [write_other _ _ twReg wsReg (by decide),write_at]
end Model
