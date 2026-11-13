import DiophantineConsistency.Sign14Positive74Model

/-! SOURCE-ONLY: explicit positive-witness formulation of the shift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_exists_iff (p : Fin 4 → ℤ) :
    (∃ u : Fin 14 → V, (∀ i, 0 < u i) ∧ InternalZero (Sign14Positive74.expression p) u) ↔
      ∃ w : Fin 14 → V, InternalZero (Sign14Optimized86Expression.expression p) w := by
  constructor
  · rintro ⟨u, hu, hz⟩
    let w : Fin 14 → V := fun i => u i - 1
    have hw : (fun i => w i + 1) = u := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hu i))
    refine ⟨w, (Sign14Positive74Model.zero_iff p w).mp ?_⟩
    apply (internalZero_positiveShift _ w).mpr
    simpa only [hw] using hz
  · rintro ⟨w, hw⟩
    refine ⟨(fun i => w i + 1), ?_, ?_⟩
    · intro i
      exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
    · exact (internalZero_positiveShift _ w).mp ((Sign14Positive74Model.zero_iff p w).mpr hw)
end DiophantineConsistency.Sign14Positive74Witness
#print axioms DiophantineConsistency.Sign14Positive74Witness.positive_zero_exists_iff
