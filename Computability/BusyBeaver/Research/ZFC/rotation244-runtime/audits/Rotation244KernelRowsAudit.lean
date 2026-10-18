import BusyBeaver.ZFC.Rotation244KernelRows
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.dispatchRotation244_eq
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old109_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old109_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old112_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old112_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old131_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old131_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old255_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old255_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old48_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old63_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old63_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old73_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old73_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old75_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old75_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old83_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old83_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old95_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation244_old95_true

example : dispatchRotation244 = 87 := dispatchRotation244_eq

example :
    machineRotation244.transition (oldStateRotation244 131) true =
      ⟨false, .left, some (oldStateRotation244 112)⟩ := rowRotation244_old131_true

example :
    machineRotation244.transition (oldStateRotation244 75) false =
      ⟨true, .right, some (oldStateRotation244 255)⟩ := rowRotation244_old75_false
