import DiophantineConsistency.AdaptiveAQ33Maps
import DiophantineConsistency.AdaptiveAQ33Literal
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ33Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveAQ33Context AdaptiveAQ33Literal AdaptiveAQ33Zeros AdaptiveAQ33Positive AdaptiveAQ33Maps AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_inputs (p : Fin 4 → ℕ) (v : Fin 34 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ34Literal.literal (fun j => (p j:ℤ))) v) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v)) := by
  have hlt := signed_w_positive p v hv hz
  have hm : magnitude (v 18,v 19) = v 18-v 19 := by simp [magnitude,tsub_eq_zero_of_le (le_of_lt hlt)]
  intro i
  cases i with
  | inl i =>
    cases i
    have he : v 18 = v 19 + magnitude (v 18,v 19) := by
      rw [hm,add_comm]
      exact (tsub_add_cancel_of_le (le_of_lt hlt)).symm
    simpa [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project,HSub.hSub,Sub.sub] using he
  | inr i =>
    change Equivalent (natural (v (oldRest i))) (natural (project v (newRest i)))
    rw [project_rest]
    exact equivalent_refl _

theorem extend_inputs (v : Fin 33 → V) :
    ∀ i, Equivalent (splitEval (oldFill i) (extend v)) (splitEval (newFill i) v) := by
  intro i
  cases i with
  | inl i =>
    cases i
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend,HSub.hSub,Sub.sub,add_comm]
  | inr i =>
    change Equivalent (natural (extend v (oldRest i))) (natural (v (newRest i)))
    rw [extend_rest]
    exact equivalent_refl _

theorem project_zero (p : Fin 4 → ℕ) (v : Fin 34 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ34Literal.literal (fun j => (p j:ℤ))) v) :
    InternalZero (AdaptiveAQ33Literal.literal (fun j => (p j:ℤ))) (project v) := by
  rw [← old_literal] at hz
  rw [← new_literal]
  exact (equivalent_zero_iff (subst_equiv_hetero (sum (fun j => (p j:ℤ))) oldFill newFill v (project v) (project_inputs p v hv (by rw [← old_literal]; exact hz)))).mp hz

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 33 → V) :
    InternalZero (AdaptiveAQ34Literal.literal p) (extend v) ↔ InternalZero (AdaptiveAQ33Literal.literal p) v := by
  rw [← old_literal, ← new_literal]
  exact equivalent_zero_iff (subst_equiv_hetero (sum p) oldFill newFill (extend v) v (extend_inputs v))
#print axioms project_zero
#print axioms extend_zero
end DiophantineConsistency.AdaptiveAQ33Transport
