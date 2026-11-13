import DiophantineConsistency.Sign16ReverseBridge
import DiophantineConsistency.Sign16VLift

/-! SOURCE-ONLY same-input seed equivalence under represented ports and bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta K MC MF x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta) :
    (∃ v : Fin 17 → V, v 0 = x ∧ InternalZero (SharingSeed16Degree112.seed p) v) ↔
      ∃ v : Fin 18 → V, v 0 = x ∧ InternalZero (SharingSeed17Degree96.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨gap, hg⟩ := Sign16VLift.exists_v_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
    refine ⟨Sign16Coordinate.lift v gap, ?_, Sign16ZeroBridge.forward p beta v gap hp0 hg hz⟩
    simpa [Sign16Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign16Coordinate.drop v, ?_, Sign16ZeroBridge.backward p beta v hp0 hz⟩
    simpa [Sign16Coordinate.drop] using hv
end DiophantineConsistency.Sign16SeedIff
#print axioms DiophantineConsistency.Sign16SeedIff.exists_same_input
