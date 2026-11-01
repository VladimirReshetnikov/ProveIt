import DiophantineConsistency.AdaptiveAQ31Maps
import DiophantineConsistency.AdaptiveAQ31Literal
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ31Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveAQ31Context AdaptiveAQ31Literal AdaptiveAQ31Maps AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_inputs (v : Fin 32 → V) (hlt : v 24 < v 23) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v)) := by
  have hm : magnitude (v 23,v 24) = v 23-v 24 := by simp [magnitude,tsub_eq_zero_of_le (le_of_lt hlt)]
  intro i
  cases i with
  | inl i =>
    cases i
    have he : v 23 = v 24 + magnitude (v 23,v 24) := by
      rw [hm,add_comm]
      exact (tsub_add_cancel_of_le (le_of_lt hlt)).symm
    simpa [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project,HSub.hSub,Sub.sub] using he
  | inr i =>
    change Equivalent (natural (v (oldRest i))) (natural (project v (newRest i)))
    rw [project_rest]
    exact equivalent_refl _

theorem extend_inputs (v : Fin 31 → V) :
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

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 32 → V) (hlt : v 24 < v 23)
    (hz : InternalZero (AdaptiveAQ32Literal.literal p) v) :
    InternalZero (AdaptiveAQ31Literal.literal p) (project v) := by
  rw [← old_literal] at hz
  rw [← new_literal]
  exact (equivalent_zero_iff (subst_equiv_hetero (sum p) oldFill newFill v (project v) (project_inputs v hlt))).mp hz

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 31 → V) :
    InternalZero (AdaptiveAQ32Literal.literal p) (extend v) ↔ InternalZero (AdaptiveAQ31Literal.literal p) v := by
  rw [← old_literal, ← new_literal]
  exact equivalent_zero_iff (subst_equiv_hetero (sum p) oldFill newFill (extend v) v (extend_inputs v))
#print axioms project_zero
#print axioms extend_zero
end DiophantineConsistency.AdaptiveAQ31Transport
