import BusyBeaver.ZFC.FastTableRotation244

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC FastTableRotation244

#print axioms SetTheory.BusyBeaver.ZFC.FastTableRotation244.fast_transition_eq
#print axioms SetTheory.BusyBeaver.ZFC.FastTableRotation244.fastMachine_eq

example (q : Fin 244) (b : Bool) :
    fastMachine.transition q b = machineRotation244.transition q b := fast_transition_eq q b

example : fastMachine = machineRotation244 := fastMachine_eq

example : fastMachine.transition (oldStateRotation244 77) true =
    ⟨true, .right, none⟩ := by
  rw [fast_transition_eq]
  exact machineRotation244_halt_action

example (c : Config 244) (t : Nat) :
    fastMachine.runFrom c t = machineRotation244.runFrom c t := by rw [fastMachine_eq]
