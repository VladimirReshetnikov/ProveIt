import BusyBeaver.ZFC.ArithmeticControlCompare254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlCompare254
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlDispatch254 (cacheReg)
open ArithmeticControlClear254 (literalTest literalExit)
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.compareEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.compareCache_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.remainderTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.distanceTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.successEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.next_distance_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.next_clear_exit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.compare_cycle
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.joint_reach
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.distance_eq_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.compare_body_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.distance_tail_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.compare_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254.compare_terminates

example : (source compareEntry).2=.decnz 6 := congrArg Prod.snd compareEntry_source
example : (source compareCache).2=.decnz 5 := congrArg Prod.snd compareCache_source
example : (source remainderTest).2=.decnz 6 := congrArg Prod.snd remainderTest_source
example : (source distanceTest).2=.decnz 5 := congrArg Prod.snd distanceTest_source
example : (source successEntry).2=.decnz 1 := congrArg Prod.snd successEntry_source
example : remainderMove.sourceIndex=s1Reg ∧ remainderMove.targetIndex=cacheReg := ⟨rfl,rfl⟩
example : resolveControl (breakPath 1 (source literalExit).1)=fetchTest := next_clear_exit

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (file : V) (ha : regValue file s1Reg≠0) (hb : regValue file cacheReg≠0) :
    controlRun 3 (liveValue (number compareEntry : V) file)=
      liveValue (number compareEntry : V)
        (compareFile file (regValue file s1Reg-1) (regValue file cacheReg-1)) := compare_cycle file ha hb
example (file t : V) (ha : t≤regValue file s1Reg) (hb : t≤regValue file cacheReg) :
    controlRun (3*t) (liveValue (number compareEntry : V) file)=
      liveValue (number compareEntry : V)
        (compareFile file (regValue file s1Reg-t) (regValue file cacheReg-t)) := joint_reach file t ha hb
example (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number compareEntry : V) file)=
      liveValue (number distanceTest : V)
        (compareFile file 0 (distance (regValue file s1Reg) (regValue file cacheReg))) := compare_body_run file
example (file : V) :
    controlRun (2*regValue file cacheReg+1) (liveValue (number distanceTest : V) file)=
      if regValue file cacheReg=0 then
        liveValue (number successEntry : V) (put cacheReg 0 file)
      else liveValue (number fetchTest : V) (put cacheReg 0 file) := distance_tail_run file
example (file : V) :
    controlRun (3*regValue file s1Reg+2*distance (regValue file s1Reg) (regValue file cacheReg)+2)
      (liveValue (number compareEntry : V) file)=
      if regValue file s1Reg=regValue file cacheReg then
        liveValue (number successEntry : V) (compareFile file 0 0)
      else liveValue (number fetchTest : V) (compareFile file 0 0) := compare_run file
example (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number compareEntry : V) file)=
      if regValue file s1Reg=regValue file cacheReg then
        liveValue (number successEntry : V) (compareFile file 0 0)
      else liveValue (number fetchTest : V) (compareFile file 0 0) := compare_terminates file
example (file : V) (he : regValue file s1Reg=regValue file cacheReg) :
    controlRun (3*regValue file s1Reg+2) (liveValue (number compareEntry : V) file)=
      liveValue (number successEntry : V) (compareFile file 0 0) := by
  have hr := compare_run file
  rw [if_pos he] at hr
  simpa only [(distance_eq_zero _ _).mpr he,mul_zero,add_zero] using hr
example (file : V) (he : regValue file s1Reg≠regValue file cacheReg) :
    controlRun (3*regValue file s1Reg+2*distance (regValue file s1Reg) (regValue file cacheReg)+2)
      (liveValue (number compareEntry : V) file)=
      liveValue (number fetchTest : V) (compareFile file 0 0) := by
  simpa only [if_neg he] using compare_run file
example (file : V) : regValue (compareFile file 0 0) s1Reg=0 := by
  unfold compareFile put
  rw [write_other _ _ cacheReg s1Reg (by decide),write_at]
example (file : V) : regValue (compareFile file 0 0) cacheReg=0 := by
  exact write_at _ _ _
example (file : V) (q : Fin 9) (hqs : s1Reg≠q) (hqc : cacheReg≠q) :
    regValue (compareFile file 0 0) q=regValue file q := by
  unfold compareFile put
  rw [write_other _ _ cacheReg q hqc,write_other _ _ s1Reg q hqs]
end Model
