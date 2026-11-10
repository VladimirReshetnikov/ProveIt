import DiophantineConsistency.Sign17ReverseBridge
import DiophantineConsistency.Sign17GapFromSeed

/-! SOURCE-ONLY: same-input seed equivalence for positive represented beta. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) (hb : 0 < beta) :
    (∃ v : Fin 18 → V, v 0 = x ∧ InternalZero (SharingSeed17Degree96.seed p) v) ↔
      ∃ v : Fin 19 → V, v 0 = x ∧ InternalZero (SharingSeed18Degree94.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨gap, hg⟩ := Sign17GapFromSeed.exists_gap p beta v hp0 hb hz
    refine ⟨Sign17Coordinate.lift v gap, ?_, Sign17ZeroBridge.forward p v gap hg hz⟩
    simpa [Sign17Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign17Coordinate.drop v, ?_, Sign17ZeroBridge.backward p v hz⟩
    simpa [Sign17Coordinate.drop] using hv
end DiophantineConsistency.Sign17SeedIff
#print axioms DiophantineConsistency.Sign17SeedIff.exists_same_input
