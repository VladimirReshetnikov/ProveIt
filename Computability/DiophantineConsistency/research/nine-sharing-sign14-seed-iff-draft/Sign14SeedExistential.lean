import DiophantineConsistency.Sign14ReverseBridge
import DiophantineConsistency.Sign14TauLift

/-! SOURCE-ONLY same-input seed equivalence under represented ports and bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SeedIff
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
    (∃ v : Fin 15 → V, v 0 = x ∧ InternalZero (SharingSeed14Degree124.seed p) v) ↔
      ∃ v : Fin 16 → V, v 0 = x ∧ InternalZero (SharingSeed15Degree124.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨gap, hg⟩ := Sign14TauLift.exists_tau_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
    refine ⟨Sign14Coordinate.lift v gap, ?_, Sign14ZeroBridge.forward p v gap hg hz⟩
    simpa [Sign14Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign14Coordinate.drop v, ?_, Sign14ZeroBridge.backward p v hz⟩
    simpa [Sign14Coordinate.drop] using hv
end DiophantineConsistency.Sign14SeedIff
#print axioms DiophantineConsistency.Sign14SeedIff.exists_same_input
