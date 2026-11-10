import DiophantineConsistency.Sign24ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under represented beta. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (∃ v : Fin 25 → V, v 0 = x ∧ InternalZero (SharingSeed24Octic.seed p) v) ↔
      ∃ v : Fin 26 → V, v 0 = x ∧ InternalZero (SharingSeed25Octic.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign24Coordinate.lift beta v, ?_, Sign24ZeroBridge.forward p beta v hp0 hz⟩
    simpa [Sign24Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign24Coordinate.drop v, ?_, Sign24ZeroBridge.backward p beta v hp0 hz⟩
    simpa [Sign24Coordinate.drop] using hv
end DiophantineConsistency.Sign24SeedIff
#print axioms DiophantineConsistency.Sign24SeedIff.exists_same_input
