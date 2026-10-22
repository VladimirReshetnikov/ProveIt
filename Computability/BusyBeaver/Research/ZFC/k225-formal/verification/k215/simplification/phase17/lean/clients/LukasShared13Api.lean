import BusyBeaver.ZFC.Lukasiewicz

namespace LukasShared13Api
open SetTheory.BusyBeaver.ZFC
open Tarski (NF)
universe v
variable {A : Type v} {imp : A → A → A} {T : A → Prop}

theorem only_explicit_fields
    (mp : ∀ {a b : A}, T (imp a b) → T a → T b)
    (row : ∀ c u a b : A, T (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))) :
    Lukasiewicz.Implicational imp T := ⟨mp, row⟩

theorem k (h : Lukasiewicz.Implicational imp T) (a b : A) :
    T (imp a (imp b a)) := Lukasiewicz.k h a b

theorem peirce (h : Lukasiewicz.Implicational imp T) (a b : A) :
    T (imp (imp (imp a b) a) a) := Lukasiewicz.peirce h a b

theorem composition (h : Lukasiewicz.Implicational imp T) (a b c : A) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) := Lukasiewicz.composition h a b c

theorem s (h : Lukasiewicz.Implicational imp T) (a b c : A) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := Lukasiewicz.s h a b c

theorem ex_falso {Ax : NF → Prop} (a : NF) : Tarski.Thm Ax (NF.imp NF.bot a) :=
  Tarski.ex_falso a

theorem classical (Ax : NF → Prop) : Kalmar.Classical NF.imp NF.bot (Tarski.Thm Ax) :=
  Tarski.classical Ax

theorem complete {Ax : NF → Prop} (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Tarski.Sat mem e a) → ∀ e : Nat → D, Tarski.Sat mem e f) :
    Tarski.Thm Ax f := Tarski.complete f hval

#print axioms only_explicit_fields
#print axioms k
#print axioms peirce
#print axioms composition
#print axioms s
#print axioms ex_falso
#print axioms classical
#print axioms complete
end LukasShared13Api
