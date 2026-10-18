import BusyBeaver.ZFC.BisimRouting245Pilot

/-! Seven finite pilot clients only. No complete-bisimulation claim. -/
open SetTheory.BusyBeaver.ZFC
open RMBisim BisimRouting245Pilot
#print axioms BisimRouting245Pilot.initial_ok
#print axioms BisimRouting245Pilot.entry0000_ok
#print axioms BisimRouting245Pilot.entry0090_ok
#print axioms BisimRouting245Pilot.entry0103_ok
#print axioms BisimRouting245Pilot.entry0329_ok
#print axioms BisimRouting245Pilot.entry0791_ok
#print axioms BisimRouting245Pilot.entry3012_ok

example : branchOk ActualTree254.tree TreeRouting245.tree cert [] [] 0 = true := initial_ok
example : checkAt 0 = true := entry0000_ok
example : checkAt 90 = true := entry0090_ok
example : checkAt 103 = true := entry0103_ok
example : checkAt 329 = true := entry0329_ok
example : checkAt 791 = true := entry0791_ok
example : checkAt 3012 = true := entry3012_ok
