import BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachineRunFromRotation240
open ArithmeticSymbolicBoxesRotation240 (ValidValues)
open ArithmeticSymbolicStepRotation240
open ArithmeticSymbolicExecutionRotation240
open SymbolicRotation240 (Branch SConfig)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.sstep_eq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.sstep_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.actual_sstep_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.exec_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.exec_to_matches
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.value_state
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.exec_to_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.verifies_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicExecutionRotation240.verifiesHalt_sound

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (runtime : BoxRuntime (V := V))

example (br : Branch) (s : SConfig) :
    ArithmeticSymbolicStepRotation240.sstep runtime br s = SymbolicRotation240.sstep br s :=
  sstep_eq runtime br s
example (br : Branch) (s t : SConfig) (m : Bool)
    (hs : ArithmeticSymbolicStepRotation240.sstep runtime br s = some (t,m)) :
    StepSound (V := V) br s t m := sstep_sound runtime br s t m hs
example (br : Branch) (s t : SConfig) (m : Bool)
    (hs : SymbolicRotation240.sstep br s = some (t,m)) :
    StepSound (V := V) br s t m := actual_sstep_sound runtime br s t m hs
example (fuel : Nat) (br : Branch) (target : SConfig → Bool) (s t : SConfig) (moved : Bool)
    (he : SymbolicRotation240.exec fuel br target s moved = some t) :
    target t = true ∧ StepSound (V := V) br s t (!moved) := exec_sound runtime fuel br target s t moved he
example (fuel : Nat) (br : Branch) (s wanted reached : SConfig)
    (he : SymbolicRotation240.exec fuel br (fun t => SymbolicRotation240.isMatch t wanted)
      s false = some reached)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values extra gap s) = value values extra gap wanted :=
  exec_to_matches runtime fuel br s wanted reached he values hv extra gap
example (values : List V) (extra gap : V) (s : SConfig) :
    first (value values extra gap s) = stateValue s.state := value_state values extra gap s
example (fuel : Nat) (br : Branch) (s reached : SConfig)
    (he : SymbolicRotation240.exec fuel br (fun t => decide (t.state = none)) s false = some reached)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values extra gap s)) = 0 :=
  exec_to_halt runtime fuel br s reached he values hv extra gap
example (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : SymbolicRotation240.verifies fuel br s wanted = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ runFrom time (value values extra gap s) = value values extra gap wanted :=
  verifies_sound runtime fuel br s wanted he values hv extra gap
example (fuel : Nat) (br : Branch) (s : SConfig)
    (he : SymbolicRotation240.verifiesHalt fuel br s = true)
    (values : List V) (hv : ValidValues br values) (extra gap : V) :
    ∃ time : V, 0 < time ∧ first (runFrom time (value values extra gap s)) = 0 :=
  verifiesHalt_sound runtime fuel br s he values hv extra gap
