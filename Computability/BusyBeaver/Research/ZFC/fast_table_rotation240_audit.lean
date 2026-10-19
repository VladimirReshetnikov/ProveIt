import BusyBeaver.ZFC.FastTableRotation240

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC FastTableRotation240

#print axioms SetTheory.BusyBeaver.ZFC.FastTableRotation240.fast_transition_eq
#print axioms SetTheory.BusyBeaver.ZFC.FastTableRotation240.fastMachine_eq

example (q : Fin 240) (b : Bool) :
    fastMachine.transition q b = machineRotation240.transition q b := fast_transition_eq q b

example : fastMachine = machineRotation240 := fastMachine_eq

example : fastMachine.transition (oldStateRotation240 77) true =
    ⟨true, .right, none⟩ := by
  rw [fast_transition_eq]
  exact machineRotation240_halt_action

example (c : Config 240) (t : Nat) :
    fastMachine.runFrom c t = machineRotation240.runFrom c t := by rw [fastMachine_eq]
