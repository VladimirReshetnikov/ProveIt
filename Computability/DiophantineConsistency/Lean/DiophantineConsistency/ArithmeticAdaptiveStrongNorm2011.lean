import DiophantineConsistency.ArithmeticSignedPairExpressions
import DiophantineConsistency.ArithmeticAdaptivePellIndices2011

/-! The actual adaptive strong factor yields its normalized additive norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveFactorUnits2011 ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
open ArithmeticSignedPairExpressions
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact additive pair for the literal strong factor, before using its unit. -/
theorem strong_rep (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    let D : V := (3+4*a)+a*a
    let I : V := (c*c)*v 4
    Equivalent (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v)
      (1+I*I+D,D*(v 3*v 3)) := by
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eA : Expr (Fin 13) := .add (.mul (.var 6) (.var 7)) (.var 7)
  let eD : Expr (Fin 13) := .add (.add (.constant 3) (.mul (.constant 4) eA)) (.mul eA eA)
  let eI : Expr (Fin 13) := .mul (.mul eC eC) (.var 4)
  let eF : Expr (Fin 13) := .var 3
  change Equivalent (pairEval (.add (.constant 1) (.sub (.mul eI eI)
    (.mul eD (.sub (.mul eF eF) (.constant 1))))) v) _
  simp [eK,eC,eA,eD,eI,eF,pairEval,Expr.splitNatural,NatExpr.evalSemiring,
    Equivalent]
  ring

def StrongNorm (v : Fin 13 → V) : Prop :=
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let D : V := (3+4*a)+a*a
  let I : V := (c*c)*v 4
  I*I+D=D*(v 3*v 3)

/-- A positive unit at the strong factor gives the strong norm. -/
theorem strong_norm_of_unit (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hu : (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v).1 =
      (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v).2+1) : StrongNorm v := by
  have hr := strong_rep p v
  have h := represented_unit hu hr
  have h' : 1+((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4*
      ((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4)+
      ((3+4*(v 6*v 7+v 7))+(v 6*v 7+v 7)*(v 6*v 7+v 7))) =
      1+(((3+4*(v 6*v 7+v 7))+(v 6*v 7+v 7)*(v 6*v 7+v 7))*(v 3*v 3)) := by
    calc
      _=(1+((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4*
        ((v 9+v 7*(v 9+v 10))*(v 9+v 7*(v 9+v 10))*v 4))+
        ((3+4*(v 6*v 7+v 7))+(v 6*v 7+v 7)*(v 6*v 7+v 7))) := by ring
      _=_ := by rw [h]; ring
  exact add_left_cancel h'


theorem expressionAt_strong_norm (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : StrongNorm v :=
  strong_norm_of_unit p v (expressionAt_factor_units (fun j => (p j:ℤ)) v hz).2.2.2

theorem current_strong_norm (v : Fin 13 → V) (hz : InternalZero expression v) : StrongNorm v := by
  apply expressionAt_strong_norm currentPorts v
  rw [currentPorts_cast]; exact hz

theorem current_natural_strong_norm (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    StrongNorm (fun j => v j+1) :=
  current_strong_norm _ ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011
