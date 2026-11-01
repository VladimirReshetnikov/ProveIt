import DiophantineConsistency.AdaptiveZ46Rest
import DiophantineConsistency.AdaptiveSquareWitnessDirect14
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46First
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveZ46Context AdaptiveZ46Maps
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sub_zero_congr {σ τ : Type*} (a b : Expr σ) (c d : Expr τ) (v : σ → V) (w : τ → V)
    (ha : Equivalent (pairEval a v) (pairEval c w))
    (hb : Equivalent (pairEval b v) (pairEval d w)) :
    InternalZero (a-b) v ↔ InternalZero (c-d) w := by
  rw [sub_zero_iff_equiv,sub_zero_iff_equiv]
  constructor
  · intro h
    exact equivalent_trans (equivalent_symm ha) (equivalent_trans h hb)
  · intro h
    exact equivalent_trans ha (equivalent_trans h (equivalent_symm hb))

theorem first_project (p : Fin 4 → ℤ) (v : Fin 47 → V) (r : V) :
    InternalZero ((residuals p 0).subst oldFill) v ↔
      InternalZero ((residuals p 0).subst newFill) (project v r) := by
  change InternalZero (((.var 24 - .var 25)*(.var 24 - .var 25)) - (.var 33 * (1 + .var 34)) : Expr (Fin 47)) v ↔
    InternalZero ((.var 24 * .var 24) - (.var 32 * (1 + .var 33)) : Expr (Fin 46)) (project v r)
  apply sub_zero_congr
  · have h := rawSquare_rep ((.var 24 - .var 25) : Expr (Fin 47)) v
    have k := rawSquare_rep (.var 24 : Expr (Fin 46)) (project v r)
    have h' : Equivalent (pairEval (((.var 24 - .var 25) : Expr (Fin 47)) * (.var 24 - .var 25)) v)
       (natural (magnitude (v 24,v 25)*magnitude (v 24,v 25))) := by
      simpa [SignedRep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub,magnitude] using h
    have k' : Equivalent (pairEval ((.var 24 : Expr (Fin 46)) * .var 24) (project v r))
       (natural (magnitude (v 24,v 25)*magnitude (v 24,v 25))) := by
      simpa [SignedRep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,magnitude,project] using k
    exact equivalent_trans h' (equivalent_symm k')
  · simp [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project]
#print axioms first_project
end DiophantineConsistency.AdaptiveZ46First
