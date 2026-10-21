import BusyBeaver.ZFC.DomRho8

namespace DomRho8APIAudit
open SetTheory.BusyBeaver.ZFC

example (T : Nat → Prop) (h : DomRho8.DomImp T) : T 0 := h.truth
example {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ Code254.wim x y := DomRho8.le_l y h
example {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ Code254.wim x y := DomRho8.le_r x h
example (l : List Nat) (i : Nat) : DomRho8.sub l i = l.getD i 0 := rfl
example {T : Nat → Prop} (h : DomRho8.DomImp T) (a b c u : Nat) :
    T (Code254.wim (Code254.wim (Code254.wim c u) a)
      (Code254.wim (Code254.wim a c) (Code254.wim b c))) := DomRho8.rho8_all h a b c u
#print axioms DomRho8.rho8_all
end DomRho8APIAudit
