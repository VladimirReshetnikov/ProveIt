import BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252
open SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineGraphPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252
open ArithmeticSymbolicBoxesPerm252 (boxPrefix ValidValues stateValue)
open ArithmeticSymbolicExecutionPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.right_row_of_transition
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.left_row_of_transition
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.literal_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.literal_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.left_empty
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.left_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.peel_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.peel_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.empty_run_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.empty_run_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.scan_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.scan_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.box_mark
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.box_increment
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.box_zero_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.box_positive_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.box_back
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.sstep_eq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.actual_sstep_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.exec_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.exec_to_matches
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.value_state
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.exec_to_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.verifies_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionPerm252.verifiesHalt_sound

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (q : Fin 252) (next : Option (Fin 252)) (read write : Bool)
    (ht : machinePerm252.transition q read = ⟨write,.right,next⟩) :
    actionLookup (stateValue (V := V) (some q)) (digit read) = 4*stateValue next+3+digit write :=
  right_row_of_transition q next read write ht
example (q : Fin 252) (next : Option (Fin 252)) (read write : Bool)
    (ht : machinePerm252.transition q read = ⟨write,.left,next⟩) :
    actionLookup (stateValue (V := V) (some q)) (digit read) = 4*stateValue next+1+digit write :=
  left_row_of_transition q next read write ht
example (br : SymbolicPerm252.Branch) (q : Fin 252) (next : Option (Fin 252))
    (read write : Bool) (l r : List SymbolicPerm252.Segment)
    (ht : machinePerm252.transition q read = ⟨write,.right,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,.bit read::r⟩
      ⟨next,false,.bit write::l,r⟩ true := literal_right br q next read write l r ht
example (br : SymbolicPerm252.Branch) (l r : List SymbolicPerm252.Segment) :
    StepSound (V := V) br ⟨some (75 : Fin 252),false,l,.bit true::r⟩
      ⟨none,false,.bit true::l,r⟩ true :=
  literal_right br (75 : Fin 252) none true true l r (by decide)
example (br : SymbolicPerm252.Branch) (q : Option (Fin 252)) (b : Bool)
    (l r : List SymbolicPerm252.Segment) :
    StepSound (V := V) br ⟨q,true,.bit b::l,r⟩ ⟨q,false,l,.bit b::r⟩ false :=
  left_bit br q b l r
example (br : SymbolicPerm252.Branch) (q : Option (Fin 252)) (b : Bool) (a c : Nat)
    (l r : List SymbolicPerm252.Segment) :
    StepSound (V := V) br ⟨q,false,l,.run b a (c+1)::r⟩
      ⟨q,false,l,.bit b::.run b a c::r⟩ false := peel_right br q b a c l r
example (br : SymbolicPerm252.Branch) (a c : Nat) (l r : List SymbolicPerm252.Segment) :
    StepSound (V := V) br ⟨some (7 : Fin 252),true,.run true a c::l,r⟩
      ⟨some (7 : Fin 252),true,l,.run false a c::r⟩ false :=
  ArithmeticSymbolicExecutionPerm252.scan_left br (7 : Fin 252) true false a c l r (by decide)
example (br : SymbolicPerm252.Branch) (r : SymbolicPerm252.Reg)
    (l : List SymbolicPerm252.Segment) :
    StepSound (V := V) br ⟨some (RegisterMarkPerm252.skip r.val),false,l,[.box (.plain .unchanged)]⟩
      ⟨some (SymbolicPerm252.markExit r),true,l,[.box (.marked r)]⟩ false := box_mark br r l
example (br : SymbolicPerm252.Branch) (r : SymbolicPerm252.Reg)
    (l : List SymbolicPerm252.Segment) :
    StepSound (V := V) br ⟨some RegisterIncrementPerm252.seekInc,false,l,[.box (.marked r)]⟩
      ⟨some RegisterIncrementPerm252.incReturnZero,true,l,[.box (.plain (.increment r))]⟩ false :=
  box_increment br r l
example (r : SymbolicPerm252.Reg) (l : List SymbolicPerm252.Segment) :
    StepSound (V := V) (some (r,true)) ⟨some RegisterBoxesPerm252.seekDec,false,l,[.box (.marked r)]⟩
      ⟨some RegisterBoxesPerm252.returnZero,true,l,[.box (.plain .unchanged)]⟩ false :=
  box_zero_decrement r l
example (r : SymbolicPerm252.Reg) (l : List SymbolicPerm252.Segment) :
    StepSound (V := V) (some (r,false)) ⟨some RegisterBoxesPerm252.seekDec,false,l,[.box (.marked r)]⟩
      ⟨some (SymbolicPerm252.positiveExit r),true,l,[.box (.plain (.decrement r))]⟩ false :=
  box_positive_decrement r l
example (br : SymbolicPerm252.Branch) (q : Fin 252) (next : Option (Fin 252))
    (x : SymbolicPerm252.Box) (l : List SymbolicPerm252.Segment)
    (ht : machinePerm252.transition q false = ⟨false,.left,next⟩) :
    StepSound (V := V) br ⟨some q,false,l,[.box x]⟩ ⟨next,true,l,[.box x]⟩ true :=
  box_back br q next x l ht
example (br : SymbolicPerm252.Branch) (s : SymbolicPerm252.SConfig) :
    ArithmeticSymbolicExecutionPerm252.sstep (V := V) br s = SymbolicPerm252.sstep br s := sstep_eq br s
example (br : SymbolicPerm252.Branch) (s t : SymbolicPerm252.SConfig) (m : Bool)
    (hs : SymbolicPerm252.sstep br s = some (t,m)) : StepSound (V := V) br s t m :=
  actual_sstep_sound br s t m hs
example (fuel : Nat) (br : SymbolicPerm252.Branch) (target : SymbolicPerm252.SConfig → Bool)
    (s t : SymbolicPerm252.SConfig) (moved : Bool)
    (he : SymbolicPerm252.exec fuel br target s moved = some t) :
    target t = true ∧ StepSound (V := V) br s t (!moved) := exec_sound fuel br target s t moved he
example (fuel : Nat) (br : SymbolicPerm252.Branch) (s wanted : SymbolicPerm252.SConfig)
    (he : SymbolicPerm252.verifies fuel br s wanted = true)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values count gap s) = value values count gap wanted :=
  verifies_sound fuel br s wanted he values hv count gap
example (fuel : Nat) (br : SymbolicPerm252.Branch) (s : SymbolicPerm252.SConfig)
    (he : SymbolicPerm252.verifiesHalt fuel br s = true)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values count gap s)) = 0 :=
  verifiesHalt_sound fuel br s he values hv count gap
example (values : List V) (hv : ValidValues none values) (count gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values count gap
      ⟨some (75 : Fin 252),false,[],[.bit true]⟩)) = 0 :=
  verifiesHalt_sound 2 none ⟨some (75 : Fin 252),false,[],[.bit true]⟩ (by decide) values hv count gap
example (br : SymbolicPerm252.Branch) (q : Option (Fin 252)) (b : Bool)
    (l r : List SymbolicPerm252.Segment) :
    StepSound (V := V) br ⟨q,true,.run b 0 0::l,r⟩ ⟨q,true,l,r⟩ false := empty_run_left br q b l r
example (fuel : Nat) (br : SymbolicPerm252.Branch) (s wanted reached : SymbolicPerm252.SConfig)
    (he : SymbolicPerm252.exec fuel br (fun t => SymbolicPerm252.isMatch t wanted) s false = some reached)
    (values : List V) (hv : ValidValues br values) (count gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values count gap s) = value values count gap wanted :=
  exec_to_matches fuel br s wanted reached he values hv count gap
end
