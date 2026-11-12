import Ring88ToParent
import ParentTo88FirstCut

/-! Source-only 13→14 quotient-graph ring cuts. No positive witness, graph
zero, Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.RingParentTo88Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

def extend (v : Fin 13 → R) (sigma t : R) : Fin 14 → R :=
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,sigma,v 9,v 10,v 11,v 12,t]

/-- Projecting back with the original root restores the parent valuation. -/
theorem project_extend (v : Fin 13 → R) (sigma t : R) :
    Ring88ToParentDraft.project (extend v sigma t) (v 8)=v := by
  funext j
  fin_cases j <;> simp [Ring88ToParentDraft.project,extend,Function.update]

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 13 → R) (sigma t : R) :
    (P88QuotientGuarded.graph p).A1.evalRing (extend v sigma t)=
      (P88FourSquare.graph p).A1.evalRing v := by
  have h := (Ring88ToParentDraft.main_eval p (extend v sigma t) (v 8)).symm
  rwa [project_extend] at h

theorem aux_eval (p : Fin 4 → ℤ) (v : Fin 13 → R) (sigma t : R) :
    (P88QuotientGuarded.graph p).aux.evalRing (extend v sigma t)=
      (P88FourSquare.graph p).aux.evalRing v := by
  have h := (Ring88ToParentDraft.aux_eval p (extend v sigma t) (v 8)).symm
  rwa [project_extend] at h

theorem strong_eval (p : Fin 4 → ℤ) (v : Fin 13 → R) (sigma t : R) :
    (P88QuotientGuarded.graph p).gap.evalRing (extend v sigma t)=
      (P88FourSquare.graph p).gap.evalRing v := by
  have h := (Ring88ToParentDraft.strong_eval p (extend v sigma t) (v 8)).symm
  rwa [project_extend] at h

/-- Target first field as a signed square with direct first-root coordinate. -/
theorem first_eval (p : Fin 4 → ℤ) (v : Fin 13 → R) (sigma t : R) :
    let w := extend v sigma t
    (P88QuotientGuarded.graph p).A0.evalRing w =
      (Ring88ToParentDraft.scale p w*(Ring88ToParentDraft.ell w+
        Ring88ToParentDraft.k w-sigma)+w 7*Ring88ToParentDraft.b p w)^2-
        (Ring88ToParentDraft.scale p w)^2*Ring88ToParentDraft.delta w := by
  simp [P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,extend,
    Ring88ToParentDraft.scale,Ring88ToParentDraft.q3,Ring88ToParentDraft.q,
    Ring88ToParentDraft.b,Ring88ToParentDraft.k,Ring88ToParentDraft.ell,
    Ring88ToParentDraft.delta,pow_two] <;> ring

end DiophantineConsistency.RingParentTo88Draft

#print axioms DiophantineConsistency.RingParentTo88Draft.first_eval
