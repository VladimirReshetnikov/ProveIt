import RingNatural86To74
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only proposed InternalZero equivalence at arbitrary signed ports
and natural-model valuations. No physical byte or endpoint binding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural86ModelDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Same valuation and signed ports, with no positivity assumption. -/
theorem internalZero_iff (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (P86NaturalCancel.graph p).output v ↔
      InternalZero (positiveShift (P74PositiveGuard.graph p).output) v := by
  rw [ModelDifferenceRing.internalZero_iff,ModelDifferenceRing.internalZero_iff,
    RingNatural86To74Draft.output_eq_positiveShift]

end DiophantineConsistency.Natural86ModelDraft

#print axioms DiophantineConsistency.Natural86ModelDraft.internalZero_iff
