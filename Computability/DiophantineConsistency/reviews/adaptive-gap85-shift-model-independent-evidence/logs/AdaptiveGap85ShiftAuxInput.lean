import DiophantineConsistency.AdaptiveGap85ShiftMainInput

/-! Signed auxiliary-root shift in arbitrary arithmetic models. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftAuxInput
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairExpressions
open AdaptiveGap85ShiftRankRep AdaptiveGap85ShiftModelPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def auxiliaryInput (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let f : Expr (Fin 13) := .var 3
  let c : Expr (Fin 13) := .var 9+.var 7*(.var 9+.var 10)
  f*f*(.var 5*c-rankExpr p)-c

/-- The auxiliary-root input has the stated signed representation. -/
theorem auxiliary_input_rep (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let H := q*q-1
    let P := v 0*((p 2:V)+(p 3:V)*q)
    let c := v 9+v 7*(v 9+v 10)
    let rq := q*q*H+P
    let rn := (v 1*q+v 2)*H
    SignedRep (auxiliaryInput (fun j => (p j:ℤ))) v
      (v 3*v 3*(v 5*c+rn),v 3*v 3*rq+c) := by
  let q : V := 1+v 0*(p 0:V)
  let H : V := q*q-1
  let P : V := v 0*((p 2:V)+(p 3:V)*q)
  let c : V := v 9+v 7*(v 9+v 10)
  let rq : V := q*q*H+P
  let rn : V := (v 1*q+v 2)*H
  let eC : Expr (Fin 13) := .var 9+.var 7*(.var 9+.var 10)
  have hc : SignedRep eC v (natural c) := rep_add_nat (rep_var v 9)
    (rep_mul_nat (rep_var v 7) (rep_add_nat (rep_var v 9) (rep_var v 10)))
  have hR := rank_rep p v
  change SignedRep (rankExpr (fun j => (p j:ℤ))) v (rq,rn) at hR
  have hf := rep_mul_nat (rep_var v 3) (rep_var v 3)
  have ht := rep_sub (rep_mul hf (rep_sub (rep_mul_nat (rep_var v 5) hc) hR)) hc
  change SignedRep (auxiliaryInput (fun j => (p j:ℤ))) v
    (minus (multiply (natural (v 3*v 3)) (minus (natural (v 5*c)) (rq,rn))) (natural c)) at ht
  apply equivalent_trans ht
  dsimp [minus,multiply,natural,Equivalent]
  ring

/-- The actual auxiliary-root input is invariant when the old T contains
    the precise decrement and the new C has been increased accordingly. -/
theorem auxiliary_input_preserved (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hJ : w 0=v 0) (hF : w 1=v 1) (hf : w 3=v 3) (hY : w 7=v 7)
    (heta : w 9=v 9) (hzeta : w 10=v 10)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); w 2=v 2+b*c*U)
    (hT : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      v 5=w 5+b*U*(q*q-1)) :
    Equivalent (pairEval (auxiliaryInput (fun j => (p j:ℤ))) w)
      (pairEval (auxiliaryInput (fun j => (p j:ℤ))) v) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 7*(q*q)
  let H : V := q*q-1
  let P : V := v 0*((p 2:V)+(p 3:V)*q)
  let c : V := v 9+v 7*(v 9+v 10)
  let rq : V := q*q*H+P
  let rn : V := (v 1*q+v 2)*H
  let rnp : V := (v 1*q+(v 2+b*c*U))*H
  have hv := auxiliary_input_rep p v
  have hw := auxiliary_input_rep p w
  have hv' : SignedRep (auxiliaryInput (fun j => (p j:ℤ))) v
    (v 3*v 3*((w 5+b*U*H)*c+rn),v 3*v 3*rq+c) := by
    simpa only [hT,b,q,U,H,P,c,rq,rn] using hv
  have hw' : SignedRep (auxiliaryInput (fun j => (p j:ℤ))) w
    (v 3*v 3*(w 5*c+rnp),v 3*v 3*rq+c) := by
    simpa only [hJ,hF,hf,hY,heta,hzeta,hC,b,q,U,H,P,c,rq,rnp] using hw
  have he := auxiliary_root b c U H q (v 1) (v 2) (w 5) P (v 3)
  change Equivalent (v 3*v 3*(w 5*c+rnp),v 3*v 3*rq+c)
    (v 3*v 3*((w 5+b*U*H)*c+rn),v 3*v 3*rq+c) at he
  exact equivalent_trans hw' (equivalent_trans he (equivalent_symm hv'))
end DiophantineConsistency.AdaptiveGap85ShiftAuxInput
