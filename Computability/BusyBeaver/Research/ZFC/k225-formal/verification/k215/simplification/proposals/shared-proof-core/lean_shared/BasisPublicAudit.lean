import BusyBeaver.ZFC.ImplicationalBasis

namespace SharedBasisAudit

open SetTheory.BusyBeaver.ZFC

universe u
variable {α : Type u} {imp : α → α → α} {T : α → Prop}

-- Constructor and projections retain the original public argument order.
example (mp : ∀ {a b}, T (imp a b) → T a → T b)
    (rho8 : ∀ c u a b,
      T (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))) :
    Lukasiewicz.Implicational imp T := ⟨mp, rho8⟩

example (h : Lukasiewicz.Implicational imp T) :
    ∀ {a b}, T (imp a b) → T a → T b := h.mp

example (h : Lukasiewicz.Implicational imp T) :
    ∀ c u a b, T (imp (imp (imp c u) a) (imp (imp a c) (imp b c))) := h.rho8

example : ∀ (_h : Lukasiewicz.Implicational imp T) (a b : α),
    T (imp a (imp b a)) := Lukasiewicz.k

example : ∀ (_h : Lukasiewicz.Implicational imp T) (a b : α),
    T (imp (imp (imp a b) a) a) := Lukasiewicz.peirce

example : ∀ (_h : Lukasiewicz.Implicational imp T) (a b c : α),
    T (imp (imp a b) (imp (imp b c) (imp a c))) := Lukasiewicz.composition

example : ∀ (_h : Lukasiewicz.Implicational imp T) (a b c : α),
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := Lukasiewicz.s

#print axioms Lukasiewicz.k
#print axioms Lukasiewicz.peirce
#print axioms Lukasiewicz.composition
#print axioms Lukasiewicz.s

end SharedBasisAudit
