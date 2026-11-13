import DiophantineConsistency.Sign21ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under symbolic ports. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (x : V) :
    (∃ v : Fin 22 → V, v 0 = x ∧ InternalZero (SharingSeed21Degree14.seed p) v) ↔
      ∃ v : Fin 23 → V, v 0 = x ∧ InternalZero (SharingSeed22Dodecic.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign21Coordinate.lift v, ?_, Sign21ZeroBridge.forward p v hz⟩
    simpa [Sign21Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign21Coordinate.drop v, ?_, Sign21ZeroBridge.backward p v hz⟩
    simpa [Sign21Coordinate.drop] using hv
end DiophantineConsistency.Sign21SeedIff
#print axioms DiophantineConsistency.Sign21SeedIff.exists_same_input
