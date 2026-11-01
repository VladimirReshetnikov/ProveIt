import DiophantineConsistency.AdaptiveQV42Transport
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace DiophantineConsistency.AdaptiveQV42
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveQV42Maps AdaptiveQV42Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- This is an oriented-witness equivalence, not an arbitrary parent-zero equivalence. -/
theorem oriented_exists_iff (p : Fin 4 → ℤ) :
    (∃ v : Fin 43 → V, (∀ i, 0 < v i) ∧ v 26 < v 25 ∧
      InternalZero (AdaptiveZ43Context.literal p) v) ↔
    (∃ v : Fin 42 → V, (∀ i, 0 < v i) ∧
      InternalZero (AdaptiveQV42Context.literal p) v) := by
  constructor
  · rintro ⟨v, hv, hlt, hz⟩
    exact ⟨project v, project_pos v hv hlt, project_zero p v hlt hz⟩
  · rintro ⟨v, hv, hz⟩
    refine ⟨extend v, extend_pos v hv, ?_, (extend_zero p v).mpr hz⟩
    dsimp [extend]
    simpa using add_lt_add_right (hv 25) 1
#print axioms oriented_exists_iff
end DiophantineConsistency.AdaptiveQV42
