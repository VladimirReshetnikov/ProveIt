import DiophantineConsistency.AdaptiveGap85Literal
import DiophantineConsistency.ArithmeticSignedPairExpressions

/-! Signed gap and rank holes under the explicit additive coordinate relation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Holes
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticSignedPairExpressions AdaptiveGap85Literal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two literal holes agree as signed values when the old and new coordinates
satisfy the exact additive relation. No witness positivity is assumed here. -/
theorem holes_equivalent (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (h : v 1+v 13+v 2=1+v 0*(p 0:V)) :
    Equivalent (splitEval (oldGap (fun j => (p j:ℤ))) v) (splitEval newGap v) ∧
    Equivalent (splitEval (oldRank (fun j => (p j:ℤ))) v)
      (splitEval (newRank (fun j => (p j:ℤ))) v) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let eB : Expr (Fin 14) := .var 0 * .constant (p 0)
  let eQ : Expr (Fin 14) := 1+eB
  have hB : SignedRep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hF := rep_var v 1
  have ha := rep_var v 13
  have hC := rep_var v 2
  have hg : SignedRep (oldGap (fun j => (p j:ℤ))) v (q,v 1+v 13) := by
    have ht := rep_sub (rep_sub hQ hF) ha
    change SignedRep (oldGap (fun j => (p j:ℤ))) v (minus (minus (natural q) (natural (v 1))) (natural (v 13))) at ht
    simpa only [minus,natural,add_zero,zero_add] using ht
  have hg' : Equivalent (q,v 1+v 13) (natural (v 2)) := by
    change q+0=(v 1+v 13)+v 2
    simpa only [add_zero,q,b] using h.symm
  have hgap := equivalent_trans hg hg'
  have ho : SignedRep (oldRank (fun j => (p j:ℤ))) v (v 13+q*b,v 1*b) := by
    have ht := rep_add ha (rep_mul (rep_sub hQ hF) hB)
    change SignedRep (oldRank (fun j => (p j:ℤ))) v (plus (natural (v 13)) (multiply (minus (natural q) (natural (v 1))) (natural b))) at ht
    simpa only [plus,minus,natural,multiply,
      add_zero,zero_add,mul_zero,zero_mul] using ht
  have hn : SignedRep (newRank (fun j => (p j:ℤ))) v (q*q,v 1*q+v 2) := by
    have ht := rep_sub (rep_mul (rep_sub hQ hF) hQ) hC
    change SignedRep (newRank (fun j => (p j:ℤ))) v (minus (multiply (minus (natural q) (natural (v 1))) (natural q)) (natural (v 2))) at ht
    simpa only [plus,minus,natural,multiply,
      add_zero,zero_add,mul_zero,zero_mul] using ht
  have hr : Equivalent (v 13+q*b,v 1*b) (q*q,v 1*q+v 2) := by
    change (v 13+q*b)+(v 1*q+v 2)=v 1*b+q*q
    calc
      _=(v 1+v 13+v 2)+(q*b+v 1*b) := by dsimp [q]; ring
      _=q+(q*b+v 1*b) := by rw [show v 1+v 13+v 2=q from h]
      _=v 1*b+q*q := by dsimp [q]; ring
  constructor
  · change Equivalent (pairEval (oldGap (fun j => (p j:ℤ))) v) (pairEval newGap v)
    simpa [newGap,pairEval,Expr.splitNatural,NatExpr.evalSemiring,natural] using hgap
  · change Equivalent (pairEval (oldRank (fun j => (p j:ℤ))) v) (pairEval (newRank (fun j => (p j:ℤ))) v)
    exact equivalent_trans ho (equivalent_trans hr (equivalent_symm hn))
/-- The exact literal zero tests agree under the additive witness relation. -/
theorem literal_zero_iff_of_relation (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (h : v 1+v 13+v 2=1+v 0*(p 0:V)) :
    (splitEval ((AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ))).subst oldLift) v).1 =
      (splitEval ((AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ))).subst oldLift) v).2 ↔
    (splitEval ((expressionAt85 (fun j => (p j:ℤ))).subst newLift) v).1 =
      (splitEval ((expressionAt85 (fun j => (p j:ℤ))).subst newLift) v).2 := by
  obtain ⟨hg,hr⟩ := holes_equivalent p v h
  exact conditional_literal_zero_iff (fun j => (p j:ℤ)) v hg hr
end DiophantineConsistency.AdaptiveGap85Holes
