import DiophantineConsistency.Sign23ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under symbolic ports. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (x : V) :
    (∃ v : Fin 24 → V, v 0 = x ∧ InternalZero (SharingSeed23Octic.seed p) v) ↔
      ∃ v : Fin 25 → V, v 0 = x ∧ InternalZero (SharingSeed24Octic.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign23Coordinate.lift v, ?_, Sign23ZeroBridge.forward p v hz⟩
    simpa [Sign23Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign23Coordinate.drop v, ?_, Sign23ZeroBridge.backward p v hz⟩
    simpa [Sign23Coordinate.drop] using hv
end DiophantineConsistency.Sign23SeedIff
#print axioms DiophantineConsistency.Sign23SeedIff.exists_same_input
