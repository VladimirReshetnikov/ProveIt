import BusyBeaver.ZFC.ArithmeticControlMP254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlMP254
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg pairFile pair_run)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlUnpairCore254 (mpConstructorEntry)
open ArithmeticControlCompare254 (compareEntry)
open ArithmeticControlDispatch254 (mpEntry cacheReg dispatchEntry)
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.scale_cycle
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.scale_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mpConstructorCopyS2_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mpConstructorTestS1_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mpScaleTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mpScaleInc1_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mpScaleInc4_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mpScaleAgain_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mpCompareMoveTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mp_middle_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.mp_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254.dispatch_mp_run

example : (source mpConstructorCopyS2).2=.inc 7 := congrArg Prod.snd mpConstructorCopyS2_source
example : (source mpScaleTest).2=.decnz 7 := congrArg Prod.snd mpScaleTest_source
example : (source mpScaleInc4).2=.inc 1 := congrArg Prod.snd mpScaleInc4_source
example : (source mpScaleAgain).2=.cont 2 := congrArg Prod.snd mpScaleAgain_source
example : mpScale.exit=mpCompareMoveTest := by simp only [mpScale]
example : mpCompareMove.exit=compareEntry := by simp only [mpCompareMove]

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (c : Scale4Shape) (file : V) (h : regValue file s2Reg≠0) :
    controlRun 6 (liveValue (number c.test : V) file)=
      liveValue (number c.test : V)
        (put twReg (regValue file twReg+4) (put s2Reg (regValue file s2Reg-1) file)) := scale_cycle c file h
example (c : Scale4Shape) (file : V) :
    controlRun (6*regValue file s2Reg+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V)
        (put twReg (regValue file twReg+4*regValue file s2Reg) (put s2Reg 0 file)) := scale_run c file
example (file : V) :
    controlRun (6*regValue file s2Reg+1) (liveValue (number mpScaleTest : V) file)=
      liveValue (number mpCompareMoveTest : V)
        (put twReg (regValue file twReg+4*regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [mpScale] using scale_run mpScale file
example (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpConstructorEntry : V) file)=
      liveValue (number mpScaleTest : V)
        (pairFile file 0 0 (regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg))) := by
  simpa only [mpConstructorPair,mpConstructorCopy] using pair_run mpConstructorPair file
example (file : V) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpConstructorEntry : V) file)=
      liveValue (number compareEntry : V) (mpMiddleFile file) := mp_middle_run file h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number fetchTest : V) (mpFile file) := mp_run file h1 h2
example (file : V) (ha : regValue file acReg=0) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dispatchEntry : V) file)=
      liveValue (number fetchTest : V) (mpFile file) := dispatch_mp_run file ha h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (he : wim (regValue file twReg) (regValue file p1Reg)=regValue file cacheReg) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number fetchTest : V)
        (put twReg (regValue file p1Reg)
          (put wsReg (cantor 0 (regValue file wsReg)) (put cacheReg 0 file))) := by
  simpa only [mpFile,if_pos he] using mp_run file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (he : wim (regValue file twReg) (regValue file p1Reg)≠regValue file cacheReg) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number fetchTest : V) (put twReg 0 (put cacheReg 0 file)) := by
  simpa only [mpFile,if_neg he] using mp_run file h1 h2
example (file : V) : regValue (mpFile file) cacheReg=0 := by
  unfold mpFile
  split
  · unfold put
    rw [write_other _ _ twReg cacheReg (by decide),write_other _ _ wsReg cacheReg (by decide),write_at]
  · unfold put
    rw [write_other _ _ twReg cacheReg (by decide),write_at]
example (file : V) (h1 : regValue file s1Reg=0) : regValue (mpFile file) s1Reg=0 := by
  unfold mpFile
  split
  · unfold put
    rw [write_other _ _ twReg s1Reg (by decide),write_other _ _ wsReg s1Reg (by decide),
      write_other _ _ cacheReg s1Reg (by decide)]
    exact h1
  · unfold put
    rw [write_other _ _ twReg s1Reg (by decide),write_other _ _ cacheReg s1Reg (by decide)]
    exact h1
example (file : V) (h2 : regValue file s2Reg=0) : regValue (mpFile file) s2Reg=0 := by
  unfold mpFile
  split
  · unfold put
    rw [write_other _ _ twReg s2Reg (by decide),write_other _ _ wsReg s2Reg (by decide),
      write_other _ _ cacheReg s2Reg (by decide)]
    exact h2
  · unfold put
    rw [write_other _ _ twReg s2Reg (by decide),write_other _ _ cacheReg s2Reg (by decide)]
    exact h2
example (file : V) : regValue (mpFile file) p1Reg=regValue file p1Reg := by
  unfold mpFile
  split
  · unfold put
    rw [write_other _ _ twReg p1Reg (by decide),write_other _ _ wsReg p1Reg (by decide),
      write_other _ _ cacheReg p1Reg (by decide)]
  · unfold put
    rw [write_other _ _ twReg p1Reg (by decide),write_other _ _ cacheReg p1Reg (by decide)]
example (file : V) (q : Fin 9) (ht : twReg≠q) (hw : wsReg≠q) (hc : cacheReg≠q) :
    regValue (mpFile file) q=regValue file q := by
  unfold mpFile
  split
  · unfold put
    rw [write_other _ _ twReg q ht,write_other _ _ wsReg q hw,write_other _ _ cacheReg q hc]
  · unfold put
    rw [write_other _ _ twReg q ht,write_other _ _ cacheReg q hc]
example (file : V) (he : wim (regValue file twReg) (regValue file p1Reg)=regValue file cacheReg) :
    regValue (mpFile file) wsReg=cantor 0 (regValue file wsReg) := by
  rw [mpFile,if_pos he]
  unfold put
  rw [write_other _ _ twReg wsReg (by decide),write_at]
example (file : V) (he : wim (regValue file twReg) (regValue file p1Reg)≠regValue file cacheReg) :
    regValue (mpFile file) wsReg=regValue file wsReg := by
  rw [mpFile,if_neg he]
  unfold put
  rw [write_other _ _ twReg wsReg (by decide),write_other _ _ cacheReg wsReg (by decide)]
end Model
