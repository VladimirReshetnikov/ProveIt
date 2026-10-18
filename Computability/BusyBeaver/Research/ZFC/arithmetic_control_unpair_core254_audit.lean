import BusyBeaver.ZFC.ArithmeticControlUnpairCore254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlUnpairCore254
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg bodyFile bodyClock)
open ArithmeticControlParamPush254 (mpPopEntry)
open ArithmeticControlDispatch254 (mpEntry)
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.move_s2_s1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.move_s2_main
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.body_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.walk_reach
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.core_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.mpCoreIncS2_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.mpCoreTestS1_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.mpCoreAgain_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.mpCoreRestoreTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.mpConstructorEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.mp_unpair_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254.mp_initial_pop_run

example : (source mpConstructorEntry).2=.decnz 1 := congrArg Prod.snd mpConstructorEntry_source
example : (source mpCoreBreak).2=.brk 1 := congrArg Prod.snd mpCoreBreak_source
example : (source mpCoreRestoreTest).2=.decnz 7 := congrArg Prod.snd mpCoreRestoreTest_source
example : mpCore.mainIndex=wsReg := rfl
example : mpCore.exit=mpConstructorEntry := by simp only [mpCore]

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (c : UnpairCoreShape) (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.bodyMoveTest : V) file)=
      liveValue (number c.bodyContinue : V)
        (put s1Reg (regValue file s1Reg+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_s1 c file
example (c : UnpairCoreShape) (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.restoreMainTest : V) file)=
      liveValue (number c.exit : V)
        (put c.mainIndex (regValue file c.mainIndex+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_main c file
example (c : UnpairCoreShape) (file : V) :
    controlRun (bodyClock file) (liveValue (number c.bodyIncS2 : V) file)=
      liveValue (number c.readEntry : V) (bodyFile file) := body_run c file
example (c : UnpairCoreShape) (file : V) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) (t : V) (ht : t≤regValue file c.mainIndex) :
    ∃ time : V, controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.readEntry : V) (walkFile c file t) := walk_reach c file h1 h2 t ht
example (c : UnpairCoreShape) (file : V) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.exit : V)
        (put s1Reg (first (regValue file c.mainIndex))
          (put c.mainIndex (second (regValue file c.mainIndex)) file)) := core_run c file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpPopEntry : V) file)=
      liveValue (number mpConstructorEntry : V)
        (put s1Reg (first (regValue file wsReg))
          (put wsReg (second (regValue file wsReg)) file)) := mp_unpair_run file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number mpConstructorEntry : V) (mpInitialFile file) := mp_initial_pop_run file h1 h2
example (file : V) : regValue (mpInitialFile file) s1Reg=regValue file twReg := write_at _ _ _
example (file : V) : regValue (mpInitialFile file) twReg=regValue file p1Reg := by
  unfold mpInitialFile put
  rw [write_other _ _ s1Reg twReg (by decide),write_at]
example (file : V) : regValue (mpInitialFile file) wsReg=regValue file wsReg := by
  unfold mpInitialFile put
  rw [write_other _ _ s1Reg wsReg (by decide),write_other _ _ twReg wsReg (by decide)]
example (file : V) : regValue (mpInitialFile file) p1Reg=regValue file p1Reg := by
  unfold mpInitialFile put
  rw [write_other _ _ s1Reg p1Reg (by decide),write_other _ _ twReg p1Reg (by decide)]
example (file : V) (h2 : regValue file s2Reg=0) : regValue (mpInitialFile file) s2Reg=0 := by
  unfold mpInitialFile put
  rw [write_other _ _ s1Reg s2Reg (by decide),write_other _ _ twReg s2Reg (by decide)]
  exact h2
example (file : V) (q : Fin 9) (h1 : s1Reg≠q) (ht : twReg≠q) :
    regValue (mpInitialFile file) q=regValue file q := by
  unfold mpInitialFile put
  rw [write_other _ _ s1Reg q h1,write_other _ _ twReg q ht]
end Model
