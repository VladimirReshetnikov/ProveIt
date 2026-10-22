import BusyBeaver.ZFC.KCodeDom

/-! Typed compatibility clients for the shared six-goal implication core.
The three original abstract exports, four unrestricted exports, all numeric
exports, and the named-logic bridge retain their previous types. -/

namespace SharedBasisAudit
open SetTheory.BusyBeaver.ZFC

universe u
variable {A : Type u} {L : DominatedImplication.Language A} {T : A → Prop}

theorem old_core_row (h : DominatedImplication.Restricted L T) (a b c d : A) :
    T (DominatedImplication.rho8 L a b c d) :=
  DominatedImplication.rho8_all h a b c d

theorem old_core_composition (h : DominatedImplication.Restricted L T) (a b c : A) :
    T (L.imp (L.imp a b) (L.imp (L.imp b c) (L.imp a c))) :=
  DominatedImplication.composition h a b c

theorem old_core_lift (h : DominatedImplication.Restricted L T) {a b : A}
    (hab : T (L.imp a b)) (x : A) : T (L.imp (L.imp x a) (L.imp x b)) :=
  DominatedImplication.lift_right h hab x

variable {imp : A → A → A}

theorem old_k (h : Lukasiewicz.Implicational imp T) (a b : A) :
    T (imp a (imp b a)) := Lukasiewicz.k h a b

theorem old_peirce (h : Lukasiewicz.Implicational imp T) (a b : A) :
    T (imp (imp (imp a b) a) a) := Lukasiewicz.peirce h a b

theorem old_composition (h : Lukasiewicz.Implicational imp T) (a b c : A) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) := Lukasiewicz.composition h a b c

theorem old_s (h : Lukasiewicz.Implicational imp T) (a b c : A) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := Lukasiewicz.s h a b c

theorem old_numeric_row {U : Nat → Prop} (h : DomRho8.DomImp U) (a b c d : Nat) :
    U (Code254.rho8 a b c d) := DomRho8.rho8_all h a b c d

theorem old_numeric_composition {U : Nat → Prop} (h : DomRho8.DomImp U) (a b c : Nat) :
    U (Code254.wim (Code254.wim a b) (Code254.wim (Code254.wim b c) (Code254.wim a c))) :=
  DomRho8.composition h a b c

theorem old_numeric_lift {U : Nat → Prop} (h : DomRho8.DomImp U) {a b : Nat}
    (hab : U (Code254.wim a b)) (x : Nat) :
    U (Code254.wim (Code254.wim x a) (Code254.wim x b)) :=
  DomRho8.lift_right h hab x

theorem old_ex_falso {Ax : Tarski.NF → Prop} (a : Tarski.NF) :
    Tarski.Thm Ax (Tarski.NF.imp Tarski.NF.bot a) := Tarski.ex_falso a

theorem old_classical (Ax : Tarski.NF → Prop) :
    Kalmar.Classical Tarski.NF.imp Tarski.NF.bot (Tarski.Thm Ax) := Tarski.classical Ax

theorem old_complete {Ax : Tarski.NF → Prop} (f : Tarski.NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Tarski.Sat mem e a) →
        ∀ e : Nat → D, Tarski.Sat mem e f) : Tarski.Thm Ax f := Tarski.complete f hval

theorem old_code_equivalence {n : Nat} : KCodeDom.CDom n ↔ KCode222.C222 n :=
  KCodeDom.cdom_iff_c222

#print axioms old_core_row
#print axioms old_core_composition
#print axioms old_core_lift
#print axioms old_k
#print axioms old_peirce
#print axioms old_composition
#print axioms old_s
#print axioms old_numeric_row
#print axioms old_numeric_composition
#print axioms old_numeric_lift
#print axioms old_ex_falso
#print axioms old_classical
#print axioms old_complete
#print axioms old_code_equivalence

end SharedBasisAudit
