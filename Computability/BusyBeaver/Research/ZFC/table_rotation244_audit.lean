import BusyBeaver.ZFC.TableRotation244

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.rawTableRotation244_size
#print axioms SetTheory.BusyBeaver.ZFC.rawTableRotation244_transition_count
#print axioms SetTheory.BusyBeaver.ZFC.oldStateRotation244_oldLabel
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation244_start
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation244_dispatch
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation244_halt_iff
#print axioms SetTheory.BusyBeaver.ZFC.machineRotation244_halt_action

example : Machine 244 := machineRotation244
example : rawTableRotation244.size = 244 := rawTableRotation244_size
example (q : Fin 244) : oldStateRotation244 (oldLabelRotation244 q) = q :=
  oldStateRotation244_oldLabel q
example : oldStateRotation244 95 = 0 := machineRotation244_start
example : oldStateRotation244 96 = 87 := machineRotation244_dispatch
example (q : Fin 244) (b : Bool) : (machineRotation244.transition q b).next = none ↔
    q = oldStateRotation244 77 ∧ b = true := machineRotation244_halt_iff q b
example : machineRotation244.transition (oldStateRotation244 77) true =
    ⟨true, .right, none⟩ := machineRotation244_halt_action
