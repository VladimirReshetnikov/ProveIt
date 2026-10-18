import BusyBeaver.ZFC.FastTableRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC FastTableRouting245

#print axioms SetTheory.BusyBeaver.ZFC.FastTableRouting245.fast_transition_eq
#print axioms SetTheory.BusyBeaver.ZFC.FastTableRouting245.fastMachine_eq

example (q : Fin 245) (b : Bool) :
    fastMachine.transition q b = machineRouting245.transition q b := fast_transition_eq q b

example : fastMachine = machineRouting245 := fastMachine_eq

example : fastMachine.transition (oldStateRouting245 95) false =
    ⟨true, .right, some (oldStateRouting245 109)⟩ := by
  rw [fast_transition_eq]
  exact rowRouting245_old95_false

example (c : Config 245) (t : Nat) :
    fastMachine.runFrom c t = machineRouting245.runFrom c t := by rw [fastMachine_eq]
