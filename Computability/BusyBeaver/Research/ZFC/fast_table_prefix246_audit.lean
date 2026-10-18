import BusyBeaver.ZFC.FastTablePrefix246

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC FastTablePrefix246

#print axioms SetTheory.BusyBeaver.ZFC.FastTablePrefix246.fast_transition_eq
#print axioms SetTheory.BusyBeaver.ZFC.FastTablePrefix246.fastMachine_eq

example (q : Fin 246) (b : Bool) :
    fastMachine.transition q b = machinePrefix246.transition q b := fast_transition_eq q b

example : fastMachine = machinePrefix246 := fastMachine_eq

example : fastMachine.transition (oldStatePrefix246 95) false =
    ⟨true, .right, some (oldStatePrefix246 109)⟩ := by
  rw [fast_transition_eq]
  exact rowPrefix246_old95_false

example (c : Config 246) (t : Nat) :
    fastMachine.runFrom c t = machinePrefix246.runFrom c t := by rw [fastMachine_eq]
