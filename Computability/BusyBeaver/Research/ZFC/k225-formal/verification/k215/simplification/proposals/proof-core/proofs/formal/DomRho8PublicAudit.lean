import BusyBeaver.ZFC.KCodeDom

namespace SetTheory.BusyBeaver.ZFC.DomRho8PublicAudit
open Code254

theorem exact_unrestricted {T : Nat → Prop} (h : DomRho8.DomImp T)
    (a b c u : Nat) : T (Code254.rho8 a b c u) :=
  DomRho8.rho8_all h a b c u

theorem exact_composition {T : Nat → Prop} (h : DomRho8.DomImp T)
    (a b c : Nat) : T (wim (wim a b) (wim (wim b c) (wim a c))) :=
  DomRho8.composition h a b c

theorem exact_distribution {T : Nat → Prop} (h : DomRho8.DomImp T)
    (a b c : Nat) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  DomRho8.distribution h a b c

theorem exact_calculus_equivalence (n : Nat) : KCodeDom.CDom n ↔ KCode222.C222 n :=
  KCodeDom.cdom_iff_c222

#print axioms exact_unrestricted
#print axioms exact_composition
#print axioms exact_distribution
#print axioms exact_calculus_equivalence
end SetTheory.BusyBeaver.ZFC.DomRho8PublicAudit
