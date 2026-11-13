import DiophantineConsistency.Sign25ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under symbolic ports. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (x : V) :
    (∃ v : Fin 26 → V, v 0 = x ∧ InternalZero (SharingSeed25Octic.seed p) v) ↔
      ∃ v : Fin 27 → V, v 0 = x ∧ InternalZero (SharingSeed26Sextic.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign25FirstCut.lift v, ?_, Sign25ZeroBridge.forward p v hz⟩
    simpa [Sign25FirstCut.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign25CoordinateRecover.drop v, ?_, Sign25ZeroBridge.backward p v hz⟩
    simpa [Sign25CoordinateRecover.drop] using hv
end DiophantineConsistency.Sign25SeedIff
#print axioms DiophantineConsistency.Sign25SeedIff.exists_same_input
