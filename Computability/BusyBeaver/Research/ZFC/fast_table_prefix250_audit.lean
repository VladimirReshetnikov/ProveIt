import BusyBeaver.ZFC.FastTablePrefix250

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC FastTablePrefix250

#print axioms SetTheory.BusyBeaver.ZFC.FastTablePrefix250.fast_transition_eq
#print axioms SetTheory.BusyBeaver.ZFC.FastTablePrefix250.fastMachine_eq

example (q : Fin 250) (b : Bool) :
    fastMachine.transition q b = machinePrefix250.transition q b := fast_transition_eq q b

example : fastMachine = machinePrefix250 := fastMachine_eq

example : fastMachine.transition (oldStatePrefix250 97) false =
    ⟨true, .right, some (oldStatePrefix250 83)⟩ := by
  rw [fast_transition_eq]
  exact rowPrefix250_old97_false

example (c : Config 250) (t : Nat) :
    fastMachine.runFrom c t = machinePrefix250.runFrom c t := by rw [fastMachine_eq]
