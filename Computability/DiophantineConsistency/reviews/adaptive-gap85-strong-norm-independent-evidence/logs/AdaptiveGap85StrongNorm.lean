import DiophantineConsistency.AdaptiveGap85Units
import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011

/-! The actual 85 strong factor implies its additive Pell norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85StrongNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveStrongNorm2011 AdaptiveGap85Literal AdaptiveGap85Units
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem represented_unit85helper {u : Pair V} {c d : V}
    (hu : u.1=u.2+1) (hr : Equivalent u (c,d)) : c=d+1 := by
  change u.1+d=u.2+c at hr
  rw [hu] at hr
  have hh : u.2+(d+1)=u.2+c := by
    calc
      u.2+(d+1)=(u.2+1)+d := by ring
      _=u.2+c := hr
  exact (add_left_cancel hh).symm

theorem strong_rep85helper (p : Fin 4 → ℕ) (v : Fin 13 → V) :
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

theorem strong_norm_of_unit85helper (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hu : (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v).1 =
      (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v).2+1) : StrongNorm v := by
  have hr := strong_rep85helper p v
  have h := represented_unit85helper hu hr
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


theorem expressionAt_strong_norm85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) : StrongNorm v := by
  have hu := (expressionAt_factor_units85 (fun j => (p j:ℤ)) v hz).2.2.2
  change (pairEval (ArithmeticAdaptiveFactorMagnitude2011.factors (fun j => (p j:ℤ))).2.2.2 v).1 =
    (pairEval (ArithmeticAdaptiveFactorMagnitude2011.factors (fun j => (p j:ℤ))).2.2.2 v).2+1 at hu
  exact strong_norm_of_unit85helper p v hu
end DiophantineConsistency.AdaptiveGap85StrongNorm
