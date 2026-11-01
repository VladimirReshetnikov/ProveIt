import DiophantineConsistency.AdaptiveGap85ShiftRankRep
import DiophantineConsistency.AdaptiveGap85ShiftModelPairs

/-! Model-internal invariance of the main factor's rank/gamma input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftMainInput
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairExpressions
open AdaptiveGap85ShiftRankRep AdaptiveGap85ShiftModelPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def mainInput (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let q : Expr (Fin 13) := 1+.var 0*.constant (p 0)
  (.var 7*(q*q))*.var 12+rankExpr p

/-- The actual signed rank/gamma input has this signed representation. -/
theorem main_input_rep (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let U := v 7*(q*q)
    let H := q*q-1
    let P := v 0*((p 2:V)+(p 3:V)*q)
    SignedRep (mainInput (fun j => (p j:ℤ))) v
      (U*v 12+q*q*H+P,(v 1*q+v 2)*H) := by
  let q : V := 1+v 0*(p 0:V)
  let U : V := v 7*(q*q)
  let H : V := q*q-1
  let P : V := v 0*((p 2:V)+(p 3:V)*q)
  let eQ : Expr (Fin 13) := 1+.var 0*.constant (p 0)
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v)
    (rep_mul_nat (rep_var v 0) (rep_nat v (p 0)))
  have hU : SignedRep (.var 7*(eQ*eQ)) v (natural U) :=
    rep_mul_nat (rep_var v 7) (rep_mul_nat hQ hQ)
  have hr := rank_rep p v
  have ht := rep_add (rep_mul_nat hU (rep_var v 12)) hr
  change SignedRep (mainInput (fun j => (p j:ℤ))) v
    (plus (natural (U*v 12)) (q*q*H+P,(v 1*q+v 2)*H)) at ht
  simpa only [plus,natural,zero_add,add_zero,add_assoc] using ht

/-- The signed main input is invariant under the C/gamma part of the shift.
    Other coordinates are arbitrary except the ones occurring in the input. -/
theorem main_input_preserved (p : Fin 4 → ℕ) (v w : Fin 13 → V) (c : V)
    (hJ : w 0=v 0) (hF : w 1=v 1) (hY : w 7=v 7)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      w 2=v 2+b*c*U)
    (hg : let b := v 0*(p 0:V); let q := 1+b;
      w 12=v 12+b*c*(q*q-1)) :
    Equivalent (pairEval (mainInput (fun j => (p j:ℤ))) w)
      (pairEval (mainInput (fun j => (p j:ℤ))) v) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 7*(q*q)
  let H : V := q*q-1
  let P : V := v 0*((p 2:V)+(p 3:V)*q)
  have hv := main_input_rep p v
  have hw := main_input_rep p w
  change SignedRep (mainInput (fun j => (p j:ℤ))) v
    (U*v 12+q*q*H+P,(v 1*q+v 2)*H) at hv
  have hw' : SignedRep (mainInput (fun j => (p j:ℤ))) w
    (U*(v 12+b*c*H)+q*q*H+P,(v 1*q+(v 2+b*c*U))*H) := by
    simpa only [hJ,hF,hY,hC,hg,b,q,U,H,P] using hw
  have hc := main_root b c U H q (v 1) (v 2) (v 12) P
  change Equivalent (U*(v 12+b*c*H)+(q*q*H+P),
    (v 1*q+(v 2+b*c*U))*H)
    (U*v 12+(q*q*H+P),(v 1*q+v 2)*H) at hc
  have hc' : Equivalent (U*(v 12+b*c*H)+q*q*H+P,
    (v 1*q+(v 2+b*c*U))*H)
    (U*v 12+q*q*H+P,(v 1*q+v 2)*H) := by simpa only [add_assoc] using hc
  exact equivalent_trans hw' (equivalent_trans hc' (equivalent_symm hv))
end DiophantineConsistency.AdaptiveGap85ShiftMainInput
