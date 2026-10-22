import BusyBeaver.ZFC.KCodeDom
import BusyBeaver.ZFC.KThmK
import BusyBeaver.ZFC.Numeric254
open SetTheory.BusyBeaver.ZFC
universe u
example {A : Type u} {L : DominatedImplication.Language A} {T : A → Prop}
    (h : DominatedImplication.Restricted L T) (a b c v : A) :
    T (DominatedImplication.rho8 L a b c v) := DominatedImplication.rho8_all h a b c v
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b : A) : T (i a (i b a)) := Lukasiewicz.k h a b
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b c : A) :
    T (i (i a (i b c)) (i (i a b) (i a c))) := Lukasiewicz.s h a b c
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b : A) : T (i (i (i a b) a) a) := Lukasiewicz.peirce h a b
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b c : A) :
    T (i (i a b) (i (i b c) (i a c))) := Lukasiewicz.composition h a b c
example (n : Nat) : KCodeDom.CDom n ↔ KCode222.C222 n := KCodeDom.cdom_iff_c222
#print axioms DominatedImplication.rho8_all
#print axioms DominatedImplication.composition
#print axioms DominatedImplication.lift_right
#print axioms Lukasiewicz.k
#print axioms Lukasiewicz.s
#print axioms Lukasiewicz.peirce
#print axioms Lukasiewicz.composition
#print axioms DomRho8.rho8_all
#print axioms KCodeDom.cdom_iff_c222
#print axioms Tarski.complete
#print axioms KThmK.classical
#print axioms Numeric254.classical
