import DiophantineConsistency.AdaptiveAQ34First
import DiophantineConsistency.AdaptiveZ46RootAlgebra
import DiophantineConsistency.AdaptiveDirectOrdinate86Context
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ34Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveAQ34Context AdaptiveAQ34Maps AdaptiveZ46RootAlgebra
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem root_project (p : Fin 4 → ℤ) (v : Fin 35 → V) (r : V)
    (hr : Equivalent (plus (v 22,v 23) (natural (v 13*r)))
      (natural (magnitude (v 22,v 23)+v 13*(v 8)))) :
    InternalZero ((residuals p 12).subst oldFill) v ↔
      InternalZero ((residuals p 12).subst newFill) (project v r) := by
  let a : Expr (Fin 35) := .var 17 + (.var 9 + .var 10)
  let b : Expr (Fin 35) := (.var 9 + .var 10) * (.var 18 - .var 19)
  let c : Expr (Fin 35) := .var 7 * (.var 0 * .constant (p 0))
  let d : Expr (Fin 35) := (.var 18 - .var 19) * ((1 + .var 0 * .constant (p 0)) * .var 29)
  have hr' : Equivalent (plus (v 22,v 23) (natural (v 13*r)))
      (plus (natural (magnitude (v 22,v 23))) (natural (v 13*(v 8)))) := by
    simpa [plus,natural] using hr
  have h := root_invariant (v 22,v 23) (natural (magnitude (v 22,v 23))) (v 13) (v 8) r
    (pairEval a v) (pairEval b v) (pairEval c v) (pairEval d v) hr'
  change Equivalent (AdaptiveZ46RootAlgebra.residual (v 22,v 23) (v 13) (v 8) (splitEval a v) (splitEval b v) (splitEval c v) (splitEval d v))
    (AdaptiveZ46RootAlgebra.residual (natural (magnitude (v 22,v 23))) (v 13) r (splitEval a v) (splitEval b v) (splitEval c v) (splitEval d v)) at h
  have he : Equivalent (pairEval ((residuals p 12).subst oldFill) v)
      (pairEval ((residuals p 12).subst newFill) (project v r)) := by
    change Equivalent (splitEval (((.var 22 - .var 23) - ((.var 13 * (((.var 17 + (.var 9 + .var 10)) + .var 8) - ((.var 9 + .var 10)*(.var 18 - .var 19))) + .var 7 * (.var 0 * .constant (p 0))) - ((.var 18 - .var 19) * ((1 + .var 0 * .constant (p 0)) * .var 29)))) : Expr (Fin 35)) v)
      (splitEval ((.var 22 - ((.var 13 * (((.var 17 + (.var 9 + .var 10)) + .var 8) - ((.var 9 + .var 10)*(.var 18 - .var 19))) + .var 7 * (.var 0 * .constant (p 0))) - ((.var 18 - .var 19) * ((1 + .var 0 * .constant (p 0)) * .var 28)))) : Expr (Fin 34)) (project v r))
    dsimp only [a,b,c,d] at h
    simp only [splitEval_sub, splitEval_add, splitEval_mul] at h ⊢
    simpa [AdaptiveZ46RootAlgebra.residual, plus, minus, multiply, natural, splitEval,
      Expr.splitNatural, NatExpr.evalSemiring, Equivalent, pairSub, pairAdd, pairMul, pairNeg,
      project] using h
  exact equivalent_zero_iff he
#print axioms root_project
end DiophantineConsistency.AdaptiveAQ34Root
