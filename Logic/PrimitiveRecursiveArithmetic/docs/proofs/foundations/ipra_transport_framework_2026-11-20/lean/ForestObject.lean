import ConciseIPRA.PR

/-! The single-edge calculation that extends a root intertwiner, in the actual
iPRA judgment. Each map is an arithmetic term in the input plus n parameters.
There is no ambient function symbol or universal evaluator in the conclusion.
Guards and inverse equations for the concrete table implementation are
discharged by callers. -/

namespace IPRAForestObject

open LeanProofs.ConciseIPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev ev (u : PTm (n + 1)) (x : PTm n) : PTm n :=
  Syn.subst (Syn.inst x) u

theorem mapEq (u : PTm (n + 1)) {x y : PTm n}
    (p : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] ev u x ≐ ev u y :=
  Prf.eqCongr1 u p

/-- A chart for the source fibre, a chart for the target fibre and the
edge transport, all for a fixed oriented edge. -/
structure EdgeChart (n : ℕ) where
  srcOut : PTm (n+1)
  srcBack : PTm (n+1)
  tgtOut : PTm (n+1)
  tgtBack : PTm (n+1)
  edge : PTm (n+1)

abbrev mon (a : EdgeChart n) (z : PTm n) :=
  ev a.tgtBack (ev a.edge (ev a.srcOut z))

abbrev liftAt (outK k backA : PTm (n+1)) (x : PTm n) :=
  ev outK (ev k (ev backA x))

/-- Pointwise arithmetic proof of the lifted naturality square. Only the
three displayed local equations are required at this edge and element. -/
theorem liftEdge (a b : EdgeChart n) (k : PTm (n+1)) (x : PTm n)
    (srcInv : Γ ⊢[PRAAx] ev a.srcOut (ev a.srcBack x) ≐ x)
    (intertwine : Γ ⊢[PRAAx] ev k (mon a (ev a.srcBack x)) ≐
      mon b (ev k (ev a.srcBack x)))
    (tgtInv : Γ ⊢[PRAAx] ev b.tgtOut (ev b.tgtBack
      (ev b.edge (liftAt b.srcOut k a.srcBack x))) ≐
      ev b.edge (liftAt b.srcOut k a.srcBack x)) :
    Γ ⊢[PRAAx] liftAt b.tgtOut k a.tgtBack (ev a.edge x) ≐
      ev b.edge (liftAt b.srcOut k a.srcBack x) :=
  Prf.eqTrans
    (mapEq b.tgtOut (mapEq k (mapEq a.tgtBack (mapEq a.edge (Prf.eqSymm srcInv)))))
    (Prf.eqTrans (mapEq b.tgtOut intertwine) tgtInv)

/-- Object-formula version, derivable under any context.
The free variables are the provided n numerical parameters. -/
theorem liftEdgeImp (a b : EdgeChart n) (k : PTm (n+1)) (x : PTm n) :
    Γ ⊢[PRAAx]
      (ev a.srcOut (ev a.srcBack x) ≐ x) ⟶
      (ev k (mon a (ev a.srcBack x)) ≐ mon b (ev k (ev a.srcBack x))) ⟶
      (ev b.tgtOut (ev b.tgtBack (ev b.edge (liftAt b.srcOut k a.srcBack x))) ≐
        ev b.edge (liftAt b.srcOut k a.srcBack x)) ⟶
      (liftAt b.tgtOut k a.tgtBack (ev a.edge x) ≐
        ev b.edge (liftAt b.srcOut k a.srcBack x)) :=
  .impI (.impI (.impI (liftEdge a b k x Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0)))

end IPRAForestObject
