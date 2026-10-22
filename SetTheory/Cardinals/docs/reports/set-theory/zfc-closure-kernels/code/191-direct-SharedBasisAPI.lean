import BusyBeaver.ZFC.KCodeDom
import BusyBeaver.ZFC.KThmK
import BusyBeaver.ZFC.Numeric254

namespace SharedBasisAPI
open SetTheory.BusyBeaver.ZFC
open Tarski

section Generic
universe u
variable {A : Type u} {L : DominatedImplication.Language A} {T : A → Prop}
variable (h : DominatedImplication.Restricted L T)
include h

theorem old_row (a b c v : A) : T (DominatedImplication.rho8 L a b c v) :=
  DominatedImplication.rho8_all h a b c v
theorem old_composition (a b c : A) :
    T (L.imp (L.imp a b) (L.imp (L.imp b c) (L.imp a c))) :=
  DominatedImplication.composition h a b c
theorem old_lift {a b : A} (hab : T (L.imp a b)) (x : A) :
    T (L.imp (L.imp x a) (L.imp x b)) :=
  DominatedImplication.lift_right h hab x

def old_language_constructor (imp : A → A → A) (below : A → A → Prop)
    (refl : ∀ a, below a a)
    (left : ∀ {v x : A} (y : A), below v x → below v (imp x y))
    (right : ∀ {v y : A} (x : A), below v y → below v (imp x y)) :
    DominatedImplication.Language A := ⟨imp, below, refl, left, right⟩
end Generic

section Unrestricted
universe u
variable {A : Type u} {imp : A → A → A} {T : A → Prop}
variable (h : Lukasiewicz.Implicational imp T)
include h

theorem old_k (a b : A) : T (imp a (imp b a)) := Lukasiewicz.k h a b
theorem old_peirce (a b : A) : T (imp (imp (imp a b) a) a) := Lukasiewicz.peirce h a b
theorem old_comp (a b c : A) : T (imp (imp a b) (imp (imp b c) (imp a c))) :=
  Lukasiewicz.composition h a b c
theorem old_s (a b c : A) : T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) :=
  Lukasiewicz.s h a b c

omit h in
theorem old_implicational_constructor
    (mp : ∀ {a b}, T (imp a b) → T a → T b)
    (row : ∀ c v a b, T (imp (imp (imp c v) a) (imp (imp a c) (imp b c)))) :
    Lukasiewicz.Implicational imp T := ⟨mp, row⟩
end Unrestricted

theorem old_numeric_row {T : Nat → Prop} (h : DomRho8.DomImp T) (a b c v : Nat) :
    T (Code254.rho8 a b c v) := DomRho8.rho8_all h a b c v

theorem old_numeric_restricted {T : Nat → Prop}
    (mp : ∀ {a b : Nat}, T (Code254.wim a b) → T a → T b)
    (row : ∀ a b c v : Nat, v ≤ a → T (Code254.rho8 a b c v)) (a b c v : Nat) :
    T (Code254.rho8 a b c v) := DomRho8.rho8_all_of_restricted mp row a b c v

theorem old_classical (Ax : NF → Prop) : Kalmar.Classical NF.imp NF.bot (Tarski.Thm Ax) :=
  Tarski.classical Ax

theorem old_ex_falso {Ax : NF → Prop} (a : NF) : Tarski.Thm Ax (NF.imp NF.bot a) :=
  Tarski.ex_falso a

theorem old_complete {Ax : NF → Prop} (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Tarski.Sat mem e a) → ∀ e : Nat → D, Tarski.Sat mem e f) :
    Tarski.Thm Ax f := Tarski.complete f hval

#print axioms old_row
#print axioms old_composition
#print axioms old_lift
#print axioms old_k
#print axioms old_peirce
#print axioms old_comp
#print axioms old_s
#print axioms old_numeric_row
#print axioms old_numeric_restricted
#print axioms old_classical
#print axioms old_ex_falso
#print axioms old_complete
#print axioms DominatedImplication.k
#print axioms DominatedImplication.peirce
#print axioms DominatedImplication.s
#print axioms KCodeDom.cdom_iff_c222
end SharedBasisAPI
