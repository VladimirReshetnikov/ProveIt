import BusyBeaver.ZFC.Rotation240KernelRows
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.dispatchRotation240_eq
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old109_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old109_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old112_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old112_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old131_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old131_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old255_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old255_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old48_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old63_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old63_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old73_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old73_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old75_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old75_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old83_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old83_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old95_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRotation240_old95_true

example : dispatchRotation240 = 84 := dispatchRotation240_eq

example :
    machineRotation240.transition (oldStateRotation240 131) true =
      ⟨false, .left, some (oldStateRotation240 112)⟩ := rowRotation240_old131_true

example :
    machineRotation240.transition (oldStateRotation240 75) false =
      ⟨true, .right, some (oldStateRotation240 255)⟩ := rowRotation240_old75_false
