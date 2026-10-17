import BusyBeaver.ZFC.ArithmeticControlRead254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlRead254 ArithmeticControlFetch254
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.CantorWalk.cantor_zero_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.CantorWalk.cantor_pred_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.CantorWalk.projections_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.CantorWalk.first_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.CantorWalk.second_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.bodyMoveTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.restorePLTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.outputTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.nextRead_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.next_body_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.move_s2_s1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.move_s2_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.move_s1_ac
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.body_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.walk_reach
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254.read_ac

section Weak
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
local instance : DecidableEq V := Classical.decEq V
example (b : V) : cantor 0 b+1=cantor (b+1) 0 := CantorWalk.cantor_zero_succ b
example (a b : V) (ha : a≠0) : cantor (a-1) (b+1)=cantor a b+1 := CantorWalk.cantor_pred_succ a b ha
example (n : V) : (first (n+1),second (n+1))=
    if first n=0 then (second n+1,0) else (first n-1,second n+1) := CantorWalk.projections_succ n
example (n : V) : first (n+1)=if first n=0 then second n+1 else first n-1 := CantorWalk.first_succ n
example (n : V) : second (n+1)=if first n=0 then 0 else second n+1 := CantorWalk.second_succ n
example (n : V) (ha : first n=0) : first (n+1)=second n+1 ∧ second (n+1)=0 :=
  CantorWalk.projections_succ_zero n ha
example (n : V) (ha : first n≠0) : first (n+1)=first n-1 ∧ second (n+1)=second n+1 :=
  CantorWalk.projections_succ_nonzero n ha
end Weak

example : source bodyMoveTest=([true,false,false,false,true,true,false,true,false],.decnz 7) := bodyMoveTest_source
example : source restorePLTest=([true,false,false,true,false],.decnz 7) := restorePLTest_source
example : source outputTest=([true,false,true,false],.decnz 6) := outputTest_source
example : source nextRead=([true,true,false,false,false,false],.decnz 8) := nextRead_source
example : resolveControl (continuePath 3 (source bodyContinue).1)=readEntry := next_body_continue

section Strong
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number bodyMoveTest : V) file)=
      liveValue (number bodyContinue : V)
        (put s1Reg (regValue file s1Reg+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_s1 file
example (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number restorePLTest : V) file)=
      liveValue (number outputTest : V)
        (put plReg (regValue file plReg+regValue file s2Reg) (put s2Reg 0 file)) := move_s2_pl file
example (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number outputTest : V) file)=
      liveValue (number nextRead : V)
        (put acReg (regValue file acReg+regValue file s1Reg) (put s1Reg 0 file)) := move_s1_ac file
example (file : V) :
    controlRun (bodyClock file) (liveValue (number bodyIncS2 : V) file)=
      liveValue (number readEntry : V) (bodyFile file) := body_run file
example (file t : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (ht : t≤regValue file plReg) :
    ∃ time : V, controlRun time (liveValue (number readEntry : V) file)=
      liveValue (number readEntry : V) (walkFile file t) := walk_reach file h1 h2 t ht
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number readEntry : V) file)=
      liveValue (number nextRead : V)
        (put acReg (regValue file acReg+first (regValue file plReg))
          (put plReg (second (regValue file plReg)) file)) := read_ac file h1 h2
example (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (ha : regValue file acReg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number readEntry : V) file)=
      liveValue (number nextRead : V)
        (put acReg (first (regValue file plReg)) (put plReg (second (regValue file plReg)) file)) := by
  simpa only [ha,zero_add] using read_ac file h1 h2
end Strong
