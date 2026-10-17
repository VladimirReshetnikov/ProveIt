import BusyBeaver.ZFC.ArithmeticControlUnpair254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlUnpair254
open ArithmeticControlNip254 ArithmeticControlDispatch254
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.move_s2_s1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.move_s2_main
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.move_s1_target
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.body_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.walk_reach
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.read_shape
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.wsBodyIncS2_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.wsRestoreMainInc_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.wsOutputInc_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.wsExit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.nipJoin_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.next_nip_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.ws_unpair
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.ws_pop
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.nip_return
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.nip_nonfalsity_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.nip_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254.dispatch_nip_run

example : source wsBodyIncS2=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false],.inc 7) := wsBodyIncS2_source
example : source wsRestoreMainInc=([true,true,true,false,true,false,false,true,false,true,true,true,false,true,true,false],.inc 2) := wsRestoreMainInc_source
example : source wsOutputInc=([true,true,true,false,true,false,false,true,false,true,true,true,true,true,false],.inc 5) := wsOutputInc_source
example : source wsExit=([true,true,true,false,true,false,false,true,true],.brk 1) := wsExit_source
example : source nipJoin=([true,true,true,false,true,true],.brk 1) := nipJoin_source
example : resolveControl (breakPath 1 (source nipJoin).1)=fetchTest := next_nip_join
example : wsRead.mainLogical=2 := by rfl
example : wsRead.mainIndex=wsReg := by rfl
example : wsRead.targetIndex=cacheReg := by rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (c : UnpairShape) (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.bodyMoveTest : V) file)=
      liveValue (number c.bodyContinue : V)
        (put s1Reg (regValue file s1Reg+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_s1 c file
example (c : UnpairShape) (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.restoreMainTest : V) file)=
      liveValue (number c.outputTest : V)
        (put c.mainIndex (regValue file c.mainIndex+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_main c file
example (c : UnpairShape) (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number c.outputTest : V) file)=
      liveValue (number c.nextRead : V)
        (put c.targetIndex (regValue file c.targetIndex+regValue file s1Reg) (put s1Reg 0 file)) := move_s1_target c file
example (c : UnpairShape) (file : V) :
    controlRun (bodyClock file) (liveValue (number c.bodyIncS2 : V) file)=
      liveValue (number c.readEntry : V) (bodyFile file) := body_run c file
example (c : UnpairShape) (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (t : V) (ht : t≤regValue file c.mainIndex) :
    ∃ time : V, controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.readEntry : V) (walkFile c file t) := walk_reach c file h1 h2 t ht
example (c : UnpairShape) (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.nextRead : V)
        (put c.targetIndex (regValue file c.targetIndex+first (regValue file c.mainIndex))
          (put c.mainIndex (second (regValue file c.mainIndex)) file)) := read_shape c file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number stackPopEntry : V) file)=
      liveValue (number wsExit : V)
        (put cacheReg (regValue file cacheReg+first (regValue file wsReg))
          (put wsReg (second (regValue file wsReg)) file)) := ws_unpair file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (hh : regValue file cacheReg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number stackPopEntry : V) file)=
      liveValue (number wsExit : V) (popFile file) := ws_pop file h1 h2 hh
example (file : V) :
    controlRun 2 (liveValue (number wsExit : V) file)=
      liveValue (number fetchTest : V) file := nip_return file
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (hh : regValue file cacheReg≠1) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number nipEntry : V) file)=
      liveValue (number fetchTest : V) (popFile file) := nip_nonfalsity_run file h1 h2 hh
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number nipEntry : V) file)=
      if regValue file cacheReg=1 then 0 else
        liveValue (number fetchTest : V) (popFile file) := nip_run file h1 h2
example (file : V) (ha : regValue file acReg=2) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dispatchEntry : V) file)=
      if regValue file cacheReg=1 then 0 else
        liveValue (number fetchTest : V) (popFile (put acReg 0 file)) := dispatch_nip_run file ha h1 h2
example (r : Fin 9 → V) (h1 : r s1Reg=0) (h2 : r s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number nipEntry : V) (fileValue r))=
      if r cacheReg=1 then 0 else
        liveValue (number fetchTest : V) (popFile (fileValue r)) := by
  have h := nip_run (fileValue r) (by simpa only [reg_file] using h1) (by simpa only [reg_file] using h2)
  simpa only [reg_file] using h
end Model
