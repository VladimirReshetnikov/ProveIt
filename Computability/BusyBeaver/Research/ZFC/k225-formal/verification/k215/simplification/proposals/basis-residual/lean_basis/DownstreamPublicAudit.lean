import BusyBeaver.ZFC.KCodeDom

open SetTheory.BusyBeaver.ZFC

-- The semantic bridge and the calculus equivalence use the unchanged clients.
#print axioms Tarski.ex_falso
#print axioms Tarski.classical
#print axioms Tarski.complete
#print axioms Code254.c254_classical
#print axioms KCode222.c222_classical
#print axioms KCodeDom.cdom_iff_c222

example {n : Nat} : KCodeDom.CDom n ↔ KCode222.C222 n :=
  KCodeDom.cdom_iff_c222
