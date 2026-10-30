import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011

/-! The actual 85 rank seed and main root represented without a sign assumption. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85SignedRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An exact signed-pair representation valid even when the rank seed is negative. -/
theorem main_root_signed85 (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let U : V := v 7*q2
    let E : V := v 6*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := E+v 7
    let H : V := 3+4*a
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    Equivalent (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v)
      (U*(v 6+a*c)+H*(U*v 12+E*q+rp+1),H*(k+rn)) := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eQ2 : Expr (Fin 13) := .mul eQ eQ
  let eU : Expr (Fin 13) := .mul (.var 7) eQ2
  let eE : Expr (Fin 13) := .mul (.var 6) (.var 7)
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eA : Expr (Fin 13) := .add eE (.var 7)
  let eH : Expr (Fin 13) := .add (.constant 3) (.mul (.constant 4) eA)
  let eG : Expr (Fin 13) := .sub (.mul (.sub eQ (.var 1)) eQ) (.var 2)
  let eR : Expr (Fin 13) := .add (.mul eG (.sub eQ2 (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let eD : Expr (Fin 13) := .add
    (.mul eU (.add (.var 6) (.mul eA eC)))
    (.mul eH (.sub (.add (.mul eU (.var 12)) (.mul eE eQ))
      (.sub (.sub eK eR) (.constant 1))))
  change Equivalent (pairEval eD v) _
  simp [eD,eR,eG,eH,eA,eC,eK,eE,eU,eQ2,eQ,eB,pairEval,Expr.splitNatural,
    NatExpr.evalSemiring,Equivalent]
  all_goals ring
end DiophantineConsistency.AdaptiveGap85SignedRank
