import BusyBeaver.ZFC.KCodeDom

namespace NumericCD52Api
open SetTheory.BusyBeaver.ZFC

variable {T : Nat → Prop}

theorem restricted_without_truth
    (mp : ∀ {a b : Nat}, T (Code254.wim a b) → T a → T b)
    (row : ∀ a b c u : Nat, u ≤ a → T (Code254.rho8 a b c u))
    (a b c u : Nat) : T (Code254.rho8 a b c u) :=
  DomRho8.rho8_all_of_restricted mp row a b c u

theorem unrestricted (h : DomRho8.DomImp T) (a b c u : Nat) :
    T (Code254.rho8 a b c u) := DomRho8.rho8_all h a b c u

theorem composition (h : DomRho8.DomImp T) (a b c : Nat) :
    T (Code254.wim (Code254.wim a b)
      (Code254.wim (Code254.wim b c) (Code254.wim a c))) :=
  DomRho8.composition h a b c

theorem lifting (h : DomRho8.DomImp T) {a b : Nat}
    (hab : T (Code254.wim a b)) (x : Nat) :
    T (Code254.wim (Code254.wim x a) (Code254.wim x b)) :=
  DomRho8.lift_right h hab x

theorem same_numeric_calculus (n : Nat) : KCodeDom.CDom n ↔ KCode222.C222 n :=
  KCodeDom.cdom_iff_c222

#print axioms restricted_without_truth
#print axioms unrestricted
#print axioms composition
#print axioms lifting
#print axioms same_numeric_calculus
end NumericCD52Api
