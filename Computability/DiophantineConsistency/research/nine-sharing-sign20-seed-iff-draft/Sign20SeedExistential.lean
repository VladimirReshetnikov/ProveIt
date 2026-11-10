import DiophantineConsistency.Sign20ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under represented beta. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (∃ v : Fin 21 → V, v 0 = x ∧ InternalZero (SharingSeed20Degree20.seed p) v) ↔
      ∃ v : Fin 22 → V, v 0 = x ∧ InternalZero (SharingSeed21Degree14.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign20Coordinate.lift beta v, ?_, Sign20ZeroBridge.forward p beta v hp0 hz⟩
    simpa [Sign20Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign20Coordinate.drop v, ?_, Sign20ZeroBridge.backward p beta v hp0 hz⟩
    simpa [Sign20Coordinate.drop] using hv
end DiophantineConsistency.Sign20SeedIff
#print axioms DiophantineConsistency.Sign20SeedIff.exists_same_input
