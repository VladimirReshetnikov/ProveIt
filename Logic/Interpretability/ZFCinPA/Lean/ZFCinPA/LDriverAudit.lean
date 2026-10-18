import ZFCinPA.LDriver

/-! Axiom audit for the `hSchema` driver (`LDriverBase`, `LNumOK`, `LDriverSteps`, `LDriver`). -/

open LeanProofs.ZFCinPA

#print axioms LDriverBase.all_iff_self
#print axioms LNumOK.numOK
#print axioms LDriverSteps.and_step
#print axioms LDriverSteps.ex_step
#print axioms LDriverSteps.all_step
#print axioms LDriverSteps.atom_step
#print axioms LDriver.driver
#print axioms LDriver.driverT
