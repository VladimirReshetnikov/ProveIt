import DiophantineConsistency.Sign22ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under symbolic ports. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (x : V) :
    (∃ v : Fin 23 → V, v 0 = x ∧ InternalZero (SharingSeed22Dodecic.seed p) v) ↔
      ∃ v : Fin 24 → V, v 0 = x ∧ InternalZero (SharingSeed23Octic.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign22Coordinate.lift v, ?_, Sign22ZeroBridge.forward p v hz⟩
    simpa [Sign22Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign22Coordinate.drop v, ?_, Sign22ZeroBridge.backward p v hz⟩
    simpa [Sign22Coordinate.drop] using hv
end DiophantineConsistency.Sign22SeedIff
#print axioms DiophantineConsistency.Sign22SeedIff.exists_same_input
