import BusyBeaver.ZFC.ArithmeticControlPair254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlPair254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.cantor_cycle
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.cantor_cycle_accumulate
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.move_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.copy_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.pair_cycle
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.pair_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.pair_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.dropPairTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.dropPairExit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.mpPairTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.mpPairExit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.drop_pair_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254.mp_pair_run

example : source dropPairTest=([true,true,true,false,true,false,true,false,true,true,false,false,false],.decnz 1) := dropPairTest_source
example : source dropPairExit=([true,true,true,false,true,false,true,false,true,true,true,false],.decnz 7) := dropPairExit_source
example : source mpPairTest=([true,true,true,true,false,false,false,false,true,true,false,false,false],.decnz 1) := mpPairTest_source
example : source mpPairExit=([true,true,true,true,false,false,false,false,true,true,true,false],.decnz 7) := mpPairExit_source
example : dropPair.copy.sourceIndex=twReg := by rfl
example : mpPair.move.sourceIndex=s1Reg := by rfl

section Scalar
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (a b n : V) (h : a+b=n+1) : cantor a b=cantor 0 n+b+1 := cantor_cycle h
example (a b n z : V) (h : a+b=n+1) : (z+b+1)+cantor 0 n=z+cantor a b := cantor_cycle_accumulate z h
end Scalar

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (c : MoveShape) (file : V) :
    controlRun (3*regValue file c.sourceIndex+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V)
        (put c.targetIndex (regValue file c.targetIndex+regValue file c.sourceIndex)
          (put c.sourceIndex 0 file)) := move_run c file
example (c : CopyShape) (file : V) :
    controlRun (4*regValue file c.sourceIndex+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V)
        (put c.secondIndex (regValue file c.secondIndex+regValue file c.sourceIndex)
          (put c.firstIndex (regValue file c.firstIndex+regValue file c.sourceIndex)
            (put c.sourceIndex 0 file))) := copy_run c file
example (c : PairShape) (file : V) (hn : regValue file s1Reg+regValue file twReg≠0) :
    controlRun (4*regValue file twReg+3*(regValue file s1Reg+regValue file twReg)+2)
      (liveValue (number c.copy.test : V) file)=
      liveValue (number c.copy.test : V)
        (pairFile file 0 (regValue file s1Reg+regValue file twReg-1)
          (regValue file s2Reg+regValue file twReg+1)) := pair_cycle c file hn
example (c : PairShape) (file : V) (ha : regValue file s1Reg=0) (hb : regValue file twReg=0) :
    controlRun 2 (liveValue (number c.copy.test : V) file)=liveValue (number c.exit : V) file := pair_zero c file ha hb
example (p : PairShape) (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number p.copy.test : V) file)=
      liveValue (number p.exit : V)
        (pairFile file 0 0
          (regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg))) := pair_run p file
example (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dropPairTest : V) file)=
      liveValue (number dropPairExit : V)
        (pairFile file 0 0
          (regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg))) := drop_pair_run file
example (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpPairTest : V) file)=
      liveValue (number mpPairExit : V)
        (pairFile file 0 0
          (regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg))) := mp_pair_run file
example (p : PairShape) (file : V) (hz : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number p.copy.test : V) file)=
      liveValue (number p.exit : V)
        (pairFile file 0 0 (cantor (regValue file s1Reg) (regValue file twReg))) := by
  simpa only [hz,zero_add] using pair_run p file
example (file : V) (hz : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dropPairTest : V) file)=
      liveValue (number dropPairExit : V)
        (pairFile file 0 0 (cantor (regValue file s1Reg) (regValue file twReg))) := by
  simpa only [hz,zero_add] using drop_pair_run file
example (file : V) (hz : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpPairTest : V) file)=
      liveValue (number mpPairExit : V)
        (pairFile file 0 0 (cantor (regValue file s1Reg) (regValue file twReg))) := by
  simpa only [hz,zero_add] using mp_pair_run file
end Model
