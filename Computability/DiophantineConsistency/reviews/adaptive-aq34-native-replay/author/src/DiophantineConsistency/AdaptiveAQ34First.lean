import DiophantineConsistency.AdaptiveAQ34Rest
import DiophantineConsistency.AdaptiveSquareWitnessDirect14
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ34First
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveAQ34Context AdaptiveAQ34Maps
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

theorem first_project (p : Fin 4 → ℤ) (v : Fin 35 → V) (r : V) :
    InternalZero ((residuals p 0).subst oldFill) v ↔
      InternalZero ((residuals p 0).subst newFill) (project v r) := by
  change InternalZero (((.var 22 - .var 23)*(.var 22 - .var 23)) - ((.var 13 * .var 13) * (1 + .var 31)) : Expr (Fin 35)) v ↔
    InternalZero ((.var 22 * .var 22) - ((.var 13 * .var 13) * (1 + .var 30)) : Expr (Fin 34)) (project v r)
  apply sub_zero_congr
  · have h := rawSquare_rep ((.var 22 - .var 23) : Expr (Fin 35)) v
    have k := rawSquare_rep (.var 22 : Expr (Fin 34)) (project v r)
    have h' : Equivalent (pairEval (((.var 22 - .var 23) : Expr (Fin 35)) * (.var 22 - .var 23)) v)
       (natural (magnitude (v 22,v 23)*magnitude (v 22,v 23))) := by
      simpa [SignedRep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub,magnitude] using h
    have k' : Equivalent (pairEval ((.var 22 : Expr (Fin 34)) * .var 22) (project v r))
       (natural (magnitude (v 22,v 23)*magnitude (v 22,v 23))) := by
      simpa [SignedRep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,magnitude,project] using k
    exact equivalent_trans h' (equivalent_symm k')
  · simp [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project]
#print axioms first_project
end DiophantineConsistency.AdaptiveAQ34First
