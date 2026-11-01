import DiophantineConsistency.AdaptiveAQ34Zeros
import DiophantineConsistency.AdaptiveZ46Orientation
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ34Norm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveAQ34Context AdaptiveAQ34Zeros AdaptiveZ46Orientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm (p : Fin 4 → ℤ) (v : Fin 35 → V)
    (hz : InternalZero (AdaptiveAQ35Literal.literal p) v) :
    magnitude (v 22,v 23)*magnitude (v 22,v 23) = (v 13)*(v 13)*(1+v 31) := by
  have hall : ∀ i : Fin 22, InternalZero ((residuals p i).subst oldFill) v :=
    (sum_zero p oldFill v).mp (by rw [old_literal]; exact hz)
  have h0 := hall 0
  change InternalZero (((.var 22 - .var 23)*(.var 22 - .var 23)) - ((.var 13 * .var 13) * (1 + .var 31)) : Expr (Fin 35)) v at h0
  let z : Expr (Fin 35) := .var 22 - .var 23
  have ha : Equivalent (pairEval (z*z) v) (pairEval ((.var 13 * .var 13) * (1 + .var 31)) v) :=
    (sub_zero_iff_equiv _ _ v).mp h0
  have hsq : Equivalent (pairEval (z*z) v) (natural (magnitude (v 22,v 23)*magnitude (v 22,v 23))) := by
    have h := rawSquare_rep z v
    simpa [SignedRep,z,pairEval,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub,magnitude] using h
  have hr : Equivalent (pairEval ((.var 13 * .var 13) * (1 + .var 31)) v) (natural ((v 13*v 13)*(1+v 31))) := by
    exact rep_mul_nat (rep_mul_nat (rep_var v 13) (rep_var v 13)) (rep_add_nat (rep_one v) (rep_var v 31))
  have hm := equivalent_trans (equivalent_symm hsq) (equivalent_trans ha hr)
  simpa [Equivalent,natural] using hm
#print axioms norm
end DiophantineConsistency.AdaptiveAQ34Norm
