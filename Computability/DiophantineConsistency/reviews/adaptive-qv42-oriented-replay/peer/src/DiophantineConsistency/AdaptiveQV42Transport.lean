import DiophantineConsistency.AdaptiveQV42Maps
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQV42Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveQV42Context AdaptiveQV42Maps AdaptiveZ46Rest
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_inputs (v : Fin 43 → V) (hlt : v 26 < v 25) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v)) := by
  have hm : magnitude (v 25,v 26) = v 25-v 26 := by simp [magnitude,tsub_eq_zero_of_le (le_of_lt hlt)]
  intro i
  cases i with
  | inl i =>
    fin_cases i
    have he : v 25 = v 26 + magnitude (v 25,v 26) := by
      rw [hm,add_comm]
      exact (tsub_add_cancel_of_le (le_of_lt hlt)).symm
    simpa [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project,HSub.hSub,Sub.sub] using he
  | inr i =>
    change Equivalent (natural (v (oldRest i))) (natural (project v (newRest i)))
    rw [project_rest]
    exact equivalent_refl _

theorem extend_inputs (v : Fin 42 → V) :
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

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 43 → V) (hlt : v 26 < v 25)
    (hz : InternalZero (AdaptiveZ43Context.literal p) v) :
    InternalZero (AdaptiveQV42Context.literal p) (project v) := by
  rw [← old_literal] at hz
  rw [← new_literal]
  exact (equivalent_zero_iff (subst_equiv_hetero (sum p) oldFill newFill v (project v) (project_inputs v hlt))).mp hz

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 42 → V) :
    InternalZero (AdaptiveZ43Context.literal p) (extend v) ↔ InternalZero (AdaptiveQV42Context.literal p) v := by
  rw [← old_literal, ← new_literal]
  exact equivalent_zero_iff (subst_equiv_hetero (sum p) oldFill newFill (extend v) v (extend_inputs v))
#print axioms project_zero
#print axioms extend_zero
end DiophantineConsistency.AdaptiveQV42Transport
