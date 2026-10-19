import BusyBeaver.ZFC.ArithmeticSymbolicBoxRuntimeRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor (first)
open ArithmeticMachineRunFromRotation240 (runFrom)
open ArithmeticSymbolicStepRotation240 (value)
open ArithmeticSymbolicBoxesRotation240 (ValidValues)
open SymbolicRotation240 (Reg Branch Segment SConfig)
open ArithmeticSymbolicBoxRuntimeRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxRuntimeRotation240.boxRuntime
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxRuntimeRotation240.verifies_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxRuntimeRotation240.verifiesHalt_sound

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : ArithmeticSymbolicStepRotation240.BoxRuntime (V := V) := boxRuntime
example (br : Branch) (r : Reg) (l : List Segment) :
    ArithmeticSymbolicStepRotation240.StepSound (V := V) br
      ⟨some (RegisterMarkRotation240.skip r.val),false,l,[.box (.plain .unchanged)]⟩
      ⟨some (SymbolicRotation240.markExit r),true,l,[.box (.marked r)]⟩ false :=
  ArithmeticSymbolicStepRotation240.box_mark boxRuntime br r l
example (br : Branch) (r : Reg) (l : List Segment) :
    ArithmeticSymbolicStepRotation240.StepSound (V := V) br
      ⟨some Rotation240Boxes.seek,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.returnZero,true,l,[.box (.plain (.increment r))]⟩ false :=
  ArithmeticSymbolicStepRotation240.box_increment boxRuntime br r l
example (r : Reg) (l : List Segment) :
    ArithmeticSymbolicStepRotation240.StepSound (V := V) (some (r,true))
      ⟨some Rotation240Boxes.carry,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.rollback,true,l,[.box (.plain .unchanged)]⟩ false :=
  ArithmeticSymbolicStepRotation240.box_zero_decrement boxRuntime r l
example (r : Reg) (l : List Segment) :
    ArithmeticSymbolicStepRotation240.StepSound (V := V) (some (r,false))
      ⟨some Rotation240Boxes.carry,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.returnZero,true,.bit true::l,[.box (.plain (.decrement r))]⟩ false :=
  ArithmeticSymbolicStepRotation240.box_positive_decrement boxRuntime r l

example (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : SymbolicRotation240.verifies fuel br s wanted = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values extra gap s) =
      value values extra gap wanted := verifies_sound fuel br s wanted he values hv extra gap
example (fuel : Nat) (br : Branch) (s : SConfig)
    (he : SymbolicRotation240.verifiesHalt fuel br s = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values extra gap s)) = 0 :=
  verifiesHalt_sound fuel br s he values hv extra gap
