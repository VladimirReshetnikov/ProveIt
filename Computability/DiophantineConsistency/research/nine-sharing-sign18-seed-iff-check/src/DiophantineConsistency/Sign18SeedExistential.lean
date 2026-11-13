import DiophantineConsistency.Sign18ReverseBridge

/-! SOURCE-ONLY: same-input seed equivalence under represented beta. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign18SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (∃ v : Fin 19 → V, v 0 = x ∧ InternalZero (SharingSeed18Degree94.seed p) v) ↔
      ∃ v : Fin 20 → V, v 0 = x ∧ InternalZero (SharingSeed19Degree44.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign18Coordinate.lift beta v, ?_, Sign18ZeroBridge.forward p beta v hp0 hz⟩
    simpa [Sign18Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign18Coordinate.drop v, ?_, Sign18ZeroBridge.backward p beta v hp0 hz⟩
    simpa [Sign18Coordinate.drop] using hv
end DiophantineConsistency.Sign18SeedIff
#print axioms DiophantineConsistency.Sign18SeedIff.exists_same_input
