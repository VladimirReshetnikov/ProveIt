import BusyBeaver.ZFC.ArithmeticControlReadTemplate254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlReadTemplate254 ArithmeticControlFetch254
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.p1Read
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.p1Read_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.p1Read_exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.p1Read_target
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.move_s2_s1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.move_s2_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.move_s1_target
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.body_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.walk_reach
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.read_shape
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.read_p1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254.reads_run

example : p1Read.targetLogical=4 := by rfl
example : p1Read.readEntry=ArithmeticControlRead254.nextRead := p1Read_entry
example : source p1Read.nextRead=([true,true,true,false,false],.decnz 3) := p1Read_exit_source
example : p1Read.targetIndex=p1Reg := p1Read_target

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (c : ReadShape) (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.bodyMoveTest : V) file)=
      liveValue (number c.bodyContinue : V)
        (put s1Reg (regValue file s1Reg+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_s1 c file
example (c : ReadShape) (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.restorePLTest : V) file)=
      liveValue (number c.outputTest : V)
        (put plReg (regValue file plReg+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_pl c file
example (c : ReadShape) (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number c.outputTest : V) file)=
      liveValue (number c.nextRead : V)
        (put c.targetIndex (regValue file c.targetIndex+regValue file s1Reg) (put s1Reg 0 file)) := move_s1_target c file
example (c : ReadShape) (file : V) :
    controlRun (bodyClock file) (liveValue (number c.bodyIncS2 : V) file)=
      liveValue (number c.readEntry : V) (bodyFile file) := body_run c file
example (c : ReadShape) (file t : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (ht : t≤regValue file plReg) :
    ∃ time : V, controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.readEntry : V) (walkFile file t) := walk_reach c file h1 h2 t ht
example (c : ReadShape) (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.nextRead : V)
        (put c.targetIndex (regValue file c.targetIndex+first (regValue file plReg))
          (put plReg (second (regValue file plReg)) file)) := read_shape c file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number ArithmeticControlRead254.nextRead : V) file)=
        liveValue (number p1Read.nextRead : V)
          (put p1Reg (regValue file p1Reg+first (regValue file plReg))
            (put plReg (second (regValue file plReg)) file)) := read_p1 file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number readEntry : V) file)=
      liveValue (number p1Read.nextRead : V)
        (put p1Reg (regValue file p1Reg+first (second (regValue file plReg)))
          (put acReg (regValue file acReg+first (regValue file plReg))
            (put plReg (second (second (regValue file plReg))) file))) := reads_run file h1 h2
example (c : ReadShape) (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (h : regValue file c.targetIndex=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.nextRead : V)
        (put c.targetIndex (first (regValue file plReg)) (put plReg (second (regValue file plReg)) file)) := by
  simpa only [h,zero_add] using read_shape c file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (h : regValue file p1Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number ArithmeticControlRead254.nextRead : V) file)=
        liveValue (number p1Read.nextRead : V)
          (put p1Reg (first (regValue file plReg)) (put plReg (second (regValue file plReg)) file)) := by
  simpa only [h,zero_add] using read_p1 file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (h : regValue file acReg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number readEntry : V) file)=
      liveValue (number p1Read.nextRead : V)
        (put p1Reg (regValue file p1Reg+first (second (regValue file plReg)))
          (put acReg (first (regValue file plReg))
            (put plReg (second (second (regValue file plReg))) file))) := by
  simpa only [h,zero_add] using reads_run file h1 h2
end Model
