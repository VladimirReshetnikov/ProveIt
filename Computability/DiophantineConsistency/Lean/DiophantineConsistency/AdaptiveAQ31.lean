import DiophantineConsistency.AdaptiveAQ31Transport
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ31
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ31Maps AdaptiveAQ31Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- This is an oriented-witness equivalence, not an arbitrary parent-zero equivalence. -/
theorem oriented_exists_iff (p : Fin 4 → ℤ) :
    (∃ v : Fin 32 → V, (∀ i, 0 < v i) ∧ v 24 < v 23 ∧
      InternalZero (AdaptiveAQ32Literal.literal p) v) ↔
    (∃ v : Fin 31 → V, (∀ i, 0 < v i) ∧
      InternalZero (AdaptiveAQ31Literal.literal p) v) := by
  constructor
  · rintro ⟨v, hv, hlt, hz⟩
    exact ⟨project v, project_pos v hv hlt, project_zero p v hlt hz⟩
  · rintro ⟨v, hv, hz⟩
    refine ⟨extend v, extend_pos v hv, ?_, (extend_zero p v).mpr hz⟩
    dsimp [extend]
    simpa using add_lt_add_right (hv 23) 1
#print axioms oriented_exists_iff
end DiophantineConsistency.AdaptiveAQ31
