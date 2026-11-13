import P78AuxRoot
import P75NegativePell

/-! Source-only same-coordinate ring identities relating 78 square residuals
and the 75 product factors. No model zero or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Ring78To75Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

/-- Four factors are literally the displayed 78 expressions. -/
theorem common_fields (p : Fin 4 → ℤ) :
    (P75NegativePell.graph p).main=1+(P78AuxRoot.graph p).A1 ∧
    (P75NegativePell.graph p).aux=(P78AuxRoot.graph p).aux ∧
    (P75NegativePell.graph p).strong=1+(P78AuxRoot.graph p).gap ∧
    (P75NegativePell.graph p).guardFactor=1+(P78AuxRoot.graph p).guardResidual := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The first factor is 1 plus the 78 first residual, over any ring. -/
theorem first_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P75NegativePell.graph p).first.evalRing v=
      1+(P78AuxRoot.graph p).A0.evalRing v := by
  simp [P75NegativePell.graph,P78AuxRoot.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat] <;> ring

/-- All five factor values in the same coordinates; no positivity or port
bounds enter these ring identities. -/
theorem factor_evals (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P75NegativePell.graph p).first.evalRing v=1+(P78AuxRoot.graph p).A0.evalRing v ∧
    (P75NegativePell.graph p).main.evalRing v=1+(P78AuxRoot.graph p).A1.evalRing v ∧
    (P75NegativePell.graph p).aux.evalRing v=(P78AuxRoot.graph p).aux.evalRing v ∧
    (P75NegativePell.graph p).strong.evalRing v=1+(P78AuxRoot.graph p).gap.evalRing v ∧
    (P75NegativePell.graph p).guardFactor.evalRing v=1+(P78AuxRoot.graph p).guardResidual.evalRing v := by
  refine ⟨first_eval p v,?_,?_,?_,?_⟩
  all_goals simp [P75NegativePell.graph,P78AuxRoot.graph,Expr.evalRing_add,
    Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,
    Expr.evalRing_ofNat]

end DiophantineConsistency.Ring78To75Draft

#print axioms DiophantineConsistency.Ring78To75Draft.factor_evals
