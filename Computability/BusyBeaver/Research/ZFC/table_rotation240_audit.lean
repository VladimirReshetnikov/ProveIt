import BusyBeaver.ZFC.TableRotation240

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.rawTableRotation240_size
#print axioms SetTheory.BusyBeaver.ZFC.rawTableRotation240_transition_count
#print axioms SetTheory.BusyBeaver.ZFC.oldStateRotation240_oldLabel
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation240_start
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation240_dispatch
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation240_halt_iff
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation240_halt_action

example : Machine 240 := machineRotation240
example : rawTableRotation240.size = 240 := rawTableRotation240_size
example (q : Fin 240) : oldStateRotation240 (oldLabelRotation240 q) = q :=
  oldStateRotation240_oldLabel q
example : oldStateRotation240 95 = 0 := machineRotation240_start
example : oldStateRotation240 96 = 84 := machineRotation240_dispatch
example (q : Fin 240) (b : Bool) : (machineRotation240.transition q b).next = none ↔
    q = oldStateRotation240 77 ∧ b = true := machineRotation240_halt_iff q b
example : machineRotation240.transition (oldStateRotation240 77) true =
    ⟨true, .right, none⟩ := machineRotation240_halt_action
