import Absorb88FirstQuotient
import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! First-factor transport for the direct-main graph draft. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First Absorb88FirstQuotient
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveTransport2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Reduced first root as a signed difference with nonnegative pieces. -/
theorem root_rep (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let ell : V := (X*Y)*(Y*k)
    let W : V := 1+k*b
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    Equivalent (pairEval (firstParts (integerPorts p)).1 v)
      (b*(v 7)+Bn*(W*q),Bp*(W*q)) := by
  let eB : Expr (Fin 12) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 12) := .add (.constant 1) eB
  let eQ3 : Expr (Fin 12) := .mul eQ (.mul eQ eQ)
  let eX : Expr (Fin 12) := .mul eQ (.var 5)
  let eY : Expr (Fin 12) := .mul eQ3 (.var 6)
  let eK : Expr (Fin 12) := .add (.var 8) (.var 9)
  let eL : Expr (Fin 12) := .mul (.mul eX eY) (.mul eY eK)
  let eC : Expr (Fin 12) := .sub (.sub eQ (.var 1)) (.var 2)
  let eA : Expr (Fin 12) := .add (.constant (p 1)) (.var 5)
  let eBt : Expr (Fin 12) := .mul eQ (.sub (.mul eC eA) (.var 1))
  let eZ : Expr (Fin 12) := .sub
    (.mul eB (.sub (.var 7) (.mul eK eBt))) eBt
  change Equivalent (pairEval eZ v) _
  simp [eZ,eBt,eA,eC,eL,eK,eY,eX,eQ3,eQ,eB,pairEval,Expr.splitNatural,
    NatExpr.evalSemiring,Equivalent]
  all_goals ring


#print axioms Absorb88Transport.root_rep
end Absorb88Transport
