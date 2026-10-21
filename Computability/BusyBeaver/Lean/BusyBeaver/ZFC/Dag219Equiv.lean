import BusyBeaver.ZFC.Dag219Bisim
import BusyBeaver.ZFC.Seed222

/-! Legacy 219-state seed endpoint, on the shared register-program bisimulation. -/

namespace SetTheory.BusyBeaver.ZFC.Dag219

open RMDag

/-- **L2 + L1 from the boot registers**: `dag219` halts iff the code 1 is derivable. -/
theorem seed_iff : IterHalts dag219 L2K.bootRegs ↔ KCode222.C222 Code254.F :=
  (iter_iff _).trans L2K.dag222_seed_iff

#print axioms seed_iff

end SetTheory.BusyBeaver.ZFC.Dag219
