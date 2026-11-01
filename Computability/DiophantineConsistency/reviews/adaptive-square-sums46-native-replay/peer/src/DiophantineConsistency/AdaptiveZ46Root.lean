import DiophantineConsistency.AdaptiveZ46First
import DiophantineConsistency.AdaptiveZ46RootAlgebra
import DiophantineConsistency.AdaptiveDirectOrdinate86Context
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveZ46Context AdaptiveZ46Maps AdaptiveZ46RootAlgebra
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem root_project (p : Fin 4 → ℤ) (v : Fin 47 → V) (r : V)
    (hr : Equivalent (plus (v 24,v 25) (natural (v 14*r)))
      (natural (magnitude (v 24,v 25)+v 14*(v 8)))) :
    InternalZero ((residuals p 14).subst oldFill) v ↔
      InternalZero ((residuals p 14).subst newFill) (project v r) := by
  let a : Expr (Fin 47) := .var 17 + (.var 9 + .var 10)
  let b : Expr (Fin 47) := .var 45 - .var 46
  let c : Expr (Fin 47) := .var 7 * (.var 0 * .constant (p 0))
  let d : Expr (Fin 47) := (.var 18 - .var 19) * .var 20
  have hr' : Equivalent (plus (v 24,v 25) (natural (v 14*r)))
      (plus (natural (magnitude (v 24,v 25))) (natural (v 14*(v 8)))) := by
    simpa [plus,natural] using hr
  have h := root_invariant (v 24,v 25) (natural (magnitude (v 24,v 25))) (v 14) (v 8) r
    (pairEval a v) (pairEval b v) (pairEval c v) (pairEval d v) hr'
  change Equivalent (AdaptiveZ46RootAlgebra.residual (v 24,v 25) (v 14) (v 8) (splitEval a v) (splitEval b v) (splitEval c v) (splitEval d v))
    (AdaptiveZ46RootAlgebra.residual (natural (magnitude (v 24,v 25))) (v 14) r (splitEval a v) (splitEval b v) (splitEval c v) (splitEval d v)) at h
  have he : Equivalent (pairEval ((residuals p 14).subst oldFill) v)
      (pairEval ((residuals p 14).subst newFill) (project v r)) := by
    change Equivalent (splitEval (((.var 24 - .var 25) - ((.var 14 * (((.var 17 + (.var 9 + .var 10)) + .var 8) - (.var 45 - .var 46)) + .var 7 * (.var 0 * .constant (p 0))) - ((.var 18 - .var 19) * .var 20))) : Expr (Fin 47)) v)
      (splitEval ((.var 24 - ((.var 14 * (((.var 17 + (.var 9 + .var 10)) + .var 8) - (.var 44 - .var 45)) + .var 7 * (.var 0 * .constant (p 0))) - ((.var 18 - .var 19) * .var 20))) : Expr (Fin 46)) (project v r))
    dsimp only [a,b,c,d] at h
    simp only [splitEval_sub, splitEval_add, splitEval_mul] at h ⊢
    simpa [AdaptiveZ46RootAlgebra.residual, plus, minus, multiply, natural, splitEval,
      Expr.splitNatural, NatExpr.evalSemiring, Equivalent, pairSub, pairAdd, pairMul, pairNeg,
      project] using h
  exact equivalent_zero_iff he
#print axioms root_project
end DiophantineConsistency.AdaptiveZ46Root
