import DiophantineConsistency.AdaptiveGap85ShiftAuxInput

/-! Signed preservation of the literal main-root shift input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftMainShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairExpressions
open AdaptiveGap85ShiftRankRep AdaptiveGap85ShiftModelPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def mainShift (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let q : Expr (Fin 13) := 1+.var 0*.constant (p 0)
  let U := .var 7*(q*q)
  let E := .var 6*.var 7
  let k := .var 9+.var 10
  U*.var 12+E*q-((k-rankExpr p)-1)

theorem main_shift_rep (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let U := v 7*(q*q)
    let H := q*q-1
    let P := v 0*((p 2:V)+(p 3:V)*q)
    let E := v 6*v 7
    let k := v 9+v 10
    SignedRep (mainShift (fun j => (p j:ℤ))) v
      (U*v 12+E*q+(q*q*H+P)+1,(v 1*q+v 2)*H+k) := by
  let q : V := 1+v 0*(p 0:V)
  let U : V := v 7*(q*q)
  let H : V := q*q-1
  let P : V := v 0*((p 2:V)+(p 3:V)*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let eQ : Expr (Fin 13) := 1+.var 0*.constant (p 0)
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v)
    (rep_mul_nat (rep_var v 0) (rep_nat v (p 0)))
  have hU : SignedRep (.var 7*(eQ*eQ)) v (natural U) := rep_mul_nat (rep_var v 7) (rep_mul_nat hQ hQ)
  have hE : SignedRep (.var 6*.var 7) v (natural E) := rep_mul_nat (rep_var v 6) (rep_var v 7)
  have hk : SignedRep (.var 9+.var 10) v (natural k) := rep_add_nat (rep_var v 9) (rep_var v 10)
  have hR := rank_rep p v
  change SignedRep (rankExpr (fun j => (p j:ℤ))) v (q*q*H+P,(v 1*q+v 2)*H) at hR
  have ht := rep_sub (rep_add (rep_mul_nat hU (rep_var v 12)) (rep_mul_nat hE hQ))
    (rep_sub (rep_sub hk hR) (rep_one v))
  change SignedRep (mainShift (fun j => (p j:ℤ))) v
    (minus (plus (natural (U*v 12)) (natural (E*q)))
      (minus (minus (natural k) (q*q*H+P,(v 1*q+v 2)*H)) (natural 1))) at ht
  apply equivalent_trans ht
  dsimp [minus,plus,natural,Equivalent]
  ring

theorem main_shift_preserved (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hJ : w 0=v 0) (hF : w 1=v 1) (hX : w 6=v 6) (hY : w 7=v 7)
    (heta : w 9=v 9) (hzeta : w 10=v 10)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); w 2=v 2+b*c*U)
    (hg : let b := v 0*(p 0:V); let q := 1+b;
      let c := v 9+v 7*(v 9+v 10); w 12=v 12+b*c*(q*q-1)) :
    Equivalent (pairEval (mainShift (fun j => (p j:ℤ))) w)
      (pairEval (mainShift (fun j => (p j:ℤ))) v) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 7*(q*q)
  let H : V := q*q-1
  let P : V := v 0*((p 2:V)+(p 3:V)*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  have hv := main_shift_rep p v
  have hw := main_shift_rep p w
  change SignedRep (mainShift (fun j => (p j:ℤ))) v
    (U*v 12+E*q+(q*q*H+P)+1,(v 1*q+v 2)*H+k) at hv
  have hw' : SignedRep (mainShift (fun j => (p j:ℤ))) w
    (U*(v 12+b*c*H)+E*q+(q*q*H+P)+1,(v 1*q+(v 2+b*c*U))*H+k) := by
    simpa only [hJ,hF,hX,hY,heta,hzeta,hC,hg,b,q,U,H,P,E,k,c] using hw
  have hc := main_root b c U H q (v 1) (v 2) (v 12) P
  change Equivalent (U*(v 12+b*c*H)+(q*q*H+P), (v 1*q+(v 2+b*c*U))*H)
    (U*v 12+(q*q*H+P),(v 1*q+v 2)*H) at hc
  have hc' : Equivalent (U*(v 12+b*c*H)+E*q+(q*q*H+P)+1,(v 1*q+(v 2+b*c*U))*H+k)
    (U*v 12+E*q+(q*q*H+P)+1,(v 1*q+v 2)*H+k) := by
    change U*(v 12+b*c*H)+(q*q*H+P)+(v 1*q+v 2)*H =
      (v 1*q+(v 2+b*c*U))*H+(U*v 12+(q*q*H+P)) at hc
    change U*(v 12+b*c*H)+E*q+(q*q*H+P)+1+((v 1*q+v 2)*H+k) =
      ((v 1*q+(v 2+b*c*U))*H+k)+(U*v 12+E*q+(q*q*H+P)+1)
    calc
      _=(U*(v 12+b*c*H)+(q*q*H+P)+(v 1*q+v 2)*H)+(E*q+1+k) := by ring
      _=((v 1*q+(v 2+b*c*U))*H+(U*v 12+(q*q*H+P)))+(E*q+1+k) := by rw [hc]
      _=_ := by ring
  exact equivalent_trans hw' (equivalent_trans hc' (equivalent_symm hv))
end DiophantineConsistency.AdaptiveGap85ShiftMainShift
