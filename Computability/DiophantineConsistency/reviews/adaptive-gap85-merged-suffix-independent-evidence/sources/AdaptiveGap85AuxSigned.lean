import DiophantineConsistency.AdaptiveGap85AuxNorm
import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! The 85 auxiliary norm with the potentially signed rank represented explicitly. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85AuxSigned
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveTransport2011 AdaptiveGap85Literal AdaptiveGap85AuxNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual auxiliary root represents the rank as a formal difference, without orientation. -/
theorem aux_root_signed85 (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let c : V := v 9+v 7*(v 9+v 10)
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    Equivalent (pairEval (eV (fun j => (p j:ℤ))) v)
      ((v 3*v 3)*(v 5*c+rn),(v 3*v 3)*rp+c) := by
  simp [eV,eC,pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent]
  ring

/-- The signed auxiliary norm is obtained without assuming any rank sign. -/
theorem expressionAt_aux_signed85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let c : V := v 9+v 7*(v 9+v 10)
    let I : V := (c*c)*v 4
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    let z : V := magnitude ((v 3*v 3)*(v 5*c+rn),(v 3*v 3)*rp+c)
    I*I*z*z+v 11*v 11=1+I*I*(v 11*v 11) := by
  have h := expressionAt_aux_norm85 (fun j => (p j:ℤ)) v hz
  have he := magnitude_equivalent (aux_root_signed85 p v)
  dsimp only [AuxNorm85] at h
  rw [he] at h
  simpa only [mul_assoc] using h
end DiophantineConsistency.AdaptiveGap85AuxSigned
