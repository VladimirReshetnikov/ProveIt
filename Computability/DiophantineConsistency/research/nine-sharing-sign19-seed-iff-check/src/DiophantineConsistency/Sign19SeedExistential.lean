import DiophantineConsistency.Sign19ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under represented beta. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign19SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (∃ v : Fin 20 → V, v 0 = x ∧ InternalZero (SharingSeed19Degree44.seed p) v) ↔
      ∃ v : Fin 21 → V, v 0 = x ∧ InternalZero (SharingSeed20Degree20.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign19Coordinate.lift beta v, ?_, Sign19ZeroBridge.forward p beta v hp0 hz⟩
    simpa [Sign19Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign19Coordinate.drop v, ?_, Sign19ZeroBridge.backward p beta v hp0 hz⟩
    simpa [Sign19Coordinate.drop] using hv
end DiophantineConsistency.Sign19SeedIff
#print axioms DiophantineConsistency.Sign19SeedIff.exists_same_input
