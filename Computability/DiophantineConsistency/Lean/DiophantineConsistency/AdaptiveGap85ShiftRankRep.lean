import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.ArithmeticSignedPairExpressions

/-! Signed representation of the exact 85 rank used in the shift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftRankRep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairExpressions
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal R subexpression appearing in the main and auxiliary factors. -/
def rankExpr (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let C : Expr (Fin 13) := .var 2
  let q := 1+J*.constant (p 0)
  let G := (q-F)*q-C
  G*(q*q-1)+J*(.constant (p 2)+.constant (p 3)*q)

/-- Its signed pair, valid in arbitrary IΣ₁ models with nonnegative ports. -/
theorem rank_rep (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let q : V := 1+v 0*(p 0:V)
    let H := q*q-1
    let P := v 0*((p 2:V)+(p 3:V)*q)
    SignedRep (rankExpr (fun j => (p j:ℤ))) v
      (q*q*H+P,(v 1*q+v 2)*H) := by
  let q : V := 1+v 0*(p 0:V)
  let H := q*q-1
  let P := v 0*((p 2:V)+(p 3:V)*q)
  let eB : Expr (Fin 13) := .var 0 * .constant (p 0)
  let eQ : Expr (Fin 13) := 1+eB
  let eH : Expr (Fin 13) := eQ*eQ-1
  let eG : Expr (Fin 13) := (eQ-.var 1)*eQ-.var 2
  let eP : Expr (Fin 13) := .var 0*(.constant (p 2)+.constant (p 3)*eQ)
  have hB : SignedRep eB v (natural (v 0*(p 0:V))) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hq1 : (1:V)≤q := by dsimp [q]; exact le_add_of_nonneg_right (by simp)
  have hH : SignedRep eH v (natural H) := rep_tsub (rep_mul_nat hQ hQ) (rep_one v) (one_le_mul hq1 hq1)
  have hG : SignedRep eG v (q*q,v 1*q+v 2) := by
    have ht := rep_sub (rep_mul (rep_sub hQ (rep_var v 1)) hQ) (rep_var v 2)
    change SignedRep eG v (minus (multiply (minus (natural q) (natural (v 1))) (natural q)) (natural (v 2))) at ht
    simpa only [minus,natural,multiply,add_zero,zero_add,mul_zero,zero_mul] using ht
  have hP : SignedRep eP v (natural P) := rep_mul_nat (rep_var v 0)
    (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ))
  have ht := rep_add (rep_mul hG hH) hP
  change SignedRep (rankExpr (fun j => (p j:ℤ))) v
    (plus (multiply (q*q,v 1*q+v 2) (natural H)) (natural P)) at ht
  simpa only [plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul] using ht
end DiophantineConsistency.AdaptiveGap85ShiftRankRep
