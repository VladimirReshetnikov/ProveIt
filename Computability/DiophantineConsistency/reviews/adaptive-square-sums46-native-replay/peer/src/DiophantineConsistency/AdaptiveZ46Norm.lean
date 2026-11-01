import DiophantineConsistency.AdaptiveZ46Zeros
import DiophantineConsistency.AdaptiveZ46Orientation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46Norm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveZ46Context AdaptiveZ46Zeros AdaptiveZ46Orientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm (p : Fin 4 → ℤ) (v : Fin 47 → V)
    (hz : InternalZero (AdaptiveNamedValues47.literal p) v) :
    magnitude (v 24,v 25)*magnitude (v 24,v 25) = (v 14)*(v 14)*(1+v 34) := by
  have hall : ∀ i : Fin 33, InternalZero ((residuals p i).subst oldFill) v :=
    (sum_zero p oldFill v).mp (by rw [old_literal]; exact hz)
  have h0 := hall 0
  have h20 := hall 20
  change InternalZero (((.var 24 - .var 25)*(.var 24 - .var 25)) - (.var 33 * (1 + .var 34)) : Expr (Fin 47)) v at h0
  change InternalZero ((.var 33 - (.var 14 * .var 14)) : Expr (Fin 47)) v at h20
  have hsigma : v 33 = v 14 * v 14 := by
    simpa [InternalZero, Expr.splitNatural, NatExpr.evalSemiring, HSub.hSub, Sub.sub] using h20
  let z : Expr (Fin 47) := .var 24 - .var 25
  have ha : Equivalent (pairEval (z*z) v) (pairEval (.var 33 * (1 + .var 34)) v) :=
    (sub_zero_iff_equiv _ _ v).mp h0
  have hsq : Equivalent (pairEval (z*z) v) (natural (magnitude (v 24,v 25)*magnitude (v 24,v 25))) := by
    have h := rawSquare_rep z v
    simpa [SignedRep,z,pairEval,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub,magnitude] using h
  have hr : Equivalent (pairEval (.var 33 * (1 + .var 34)) v) (natural (v 33*(1+v 34))) := by
    simpa [SignedRep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural] using
      (equivalent_refl (natural (v 33*(1+v 34))))
  have hm := equivalent_trans (equivalent_symm hsq) (equivalent_trans ha hr)
  simpa [Equivalent,natural,hsigma] using hm
#print axioms norm
end DiophantineConsistency.AdaptiveZ46Norm
