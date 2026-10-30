import DiophantineConsistency.AdaptiveDirectOrdinate86AuxNorm
import DiophantineConsistency.AdaptiveDirectOrdinate86Witness

/-! Bind the direct-ordinate auxiliary norm to the 14-coordinate client. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86AuxNormClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveFirstRootFactor87Syntax ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86AuxNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signedV_eval (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    pairEval (eV p) (fun i => v (embed i)) = splitEval (signedV p) v := by
  change splitEval (eV p) (fun i => v (embed i)) = splitEval (signedV p) v
  simp only [eV,signedV,eC,splitEval_add,splitEval_sub,splitEval_mul]
  simp [splitEval,Expr.splitNatural,NatExpr.evalSemiring,embed,
    AdaptiveFirstRootFactor87.pairAdd,AdaptiveFirstRootFactor87.pairSub,AdaptiveFirstRootFactor87.pairMul,AdaptiveFirstRootFactor87.pairNeg]

theorem actual_norm_for_witness (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (expressionAt86 p) (fun i => v (embed i))) :
    let c : V := v 9+v 7*(v 9+v 10)
    let I : V := (c*c)*v 4
    I*I*magnitude (splitEval (signedV p) v)*magnitude (splitEval (signedV p) v)+
      v 11*v 11=1+I*I*(v 11)*(v 11) := by
  have h := expressionAt_aux_norm86 p (fun i => v (embed i)) hz
  simp only [AuxNorm86,signedV_eval,embed] at h
  exact h
end DiophantineConsistency.AdaptiveDirectOrdinate86AuxNormClient
