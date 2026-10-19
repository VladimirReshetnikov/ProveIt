import BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineGraphRotation240 ArithmeticMachineUniformScansPerm252
open ArithmeticSymbolicStepRotation240
open SymbolicRotation240 (Branch Reg Box Segment SConfig)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.right_row_of_transition
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.left_row_of_transition
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.literal_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.literal_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.left_empty
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.left_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.peel_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.peel_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.empty_run_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.empty_run_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.scan_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.scan_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.box_mark
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.box_increment
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.box_zero_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.box_positive_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicStepRotation240.box_back

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (q : Fin 240) (next : Option (Fin 240)) (read write : Bool)
    (ht : machineRotation240.transition q read = ⟨write,.right,next⟩) :
    actionLookup (stateValue (V := V) (some q)) (digit read) =
      4*stateValue next+3+digit write := right_row_of_transition q next read write ht
example (q : Fin 240) (next : Option (Fin 240)) (read write : Bool)
    (ht : machineRotation240.transition q read = ⟨write,.left,next⟩) :
    actionLookup (stateValue (V := V) (some q)) (digit read) =
      4*stateValue next+1+digit write := left_row_of_transition q next read write ht
example (br : Branch) (q : Fin 240) (next : Option (Fin 240))
    (read write : Bool) (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨write,.right,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,.bit read::r⟩
      ⟨next,false,.bit write::l,r⟩ true := literal_right br q next read write l r ht
example (br : Branch) (q : Fin 240) (next : Option (Fin 240))
    (read write : Bool) (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨write,.left,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,.bit read::r⟩
      ⟨next,true,l,.bit write::r⟩ true := literal_left br q next read write l r ht
example (br : Branch) (q : Option (Fin 240)) (r : List Segment) :
    StepSound (V := V) br ⟨q,true,[],r⟩ ⟨q,false,[],.bit false::r⟩ false := left_empty br q r
example (br : Branch) (q : Option (Fin 240)) (b : Bool) (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.bit b::l,r⟩ ⟨q,false,l,.bit b::r⟩ false := left_bit br q b l r
example (br : Branch) (q : Option (Fin 240)) (b : Bool) (a c : Nat) (l r : List Segment) :
    StepSound (V := V) br ⟨q,false,l,.run b a (c+1)::r⟩
      ⟨q,false,l,.bit b::.run b a c::r⟩ false := peel_right br q b a c l r
example (br : Branch) (q : Option (Fin 240)) (b : Bool) (a c : Nat) (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.run b a (c+1)::l,r⟩
      ⟨q,true,.bit b::.run b a c::l,r⟩ false := peel_left br q b a c l r
example (br : Branch) (q : Option (Fin 240)) (b : Bool) (l r : List Segment) :
    StepSound (V := V) br ⟨q,false,l,.run b 0 0::r⟩ ⟨q,false,l,r⟩ false := empty_run_right br q b l r
example (br : Branch) (q : Option (Fin 240)) (b : Bool) (l r : List Segment) :
    StepSound (V := V) br ⟨q,true,.run b 0 0::l,r⟩ ⟨q,true,l,r⟩ false := empty_run_left br q b l r
example (br : Branch) (q : Fin 240) (read write : Bool) (a c : Nat) (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨write,.right,some q⟩) :
    StepSound (V := V) br ⟨some q,false,l,.run read a c::r⟩
      ⟨some q,false,.run write a c::l,r⟩ false := scan_right br q read write a c l r ht
example (br : Branch) (q : Fin 240) (read write : Bool) (a c : Nat) (l r : List Segment)
    (ht : machineRotation240.transition q read = ⟨write,.left,some q⟩) :
    StepSound (V := V) br ⟨some q,true,.run read a c::l,r⟩
      ⟨some q,true,l,.run write a c::r⟩ false := scan_left br q read write a c l r ht

variable (runtime : BoxRuntime (V := V))

example (br : Branch) (r : Reg) (l : List Segment) :
    StepSound (V := V) br
      ⟨some (RegisterMarkRotation240.skip r.val),false,l,[.box (.plain .unchanged)]⟩
      ⟨some (SymbolicRotation240.markExit r),true,l,[.box (.marked r)]⟩ false := box_mark runtime br r l
example (br : Branch) (r : Reg) (l : List Segment) :
    StepSound (V := V) br ⟨some Rotation240Boxes.seek,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.returnZero,true,l,[.box (.plain (.increment r))]⟩ false :=
  box_increment runtime br r l
example (r : Reg) (l : List Segment) :
    StepSound (V := V) (some (r,true)) ⟨some Rotation240Boxes.carry,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.rollback,true,l,[.box (.plain .unchanged)]⟩ false :=
  box_zero_decrement runtime r l
example (r : Reg) (l : List Segment) :
    StepSound (V := V) (some (r,false)) ⟨some Rotation240Boxes.carry,false,l,[.box (.marked r)]⟩
      ⟨some Rotation240Boxes.returnZero,true,.bit true::l,[.box (.plain (.decrement r))]⟩ false :=
  box_positive_decrement runtime r l
example (br : Branch) (q : Fin 240) (next : Option (Fin 240)) (x : Box) (l : List Segment)
    (ht : machineRotation240.transition q false = ⟨false,.left,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,[.box x]⟩ ⟨next,true,l,[.box x]⟩ true := box_back br q next x l ht
