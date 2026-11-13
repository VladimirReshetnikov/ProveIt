import DiophantineConsistency.Sign15ReverseBridge
import DiophantineConsistency.Sign15InnerLift
import DiophantineConsistency.Sign15SignedValue

/-! SOURCE-ONLY same-input seed equivalence under represented ports and bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15SeedIff
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
    (∃ v : Fin 16 → V, v 0 = x ∧ InternalZero (SharingSeed15Degree124.seed p) v) ↔
      ∃ v : Fin 17 → V, v 0 = x ∧ InternalZero (SharingSeed16Degree112.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨gap, hg⟩ := Sign15InnerLift.exists_inner_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
    have hq := Sign15ScalarWindow.q_bound_of_seed p beta K MC MF v hp0 hp1 hb hMC hMF hz
    have he := Sign15SignedValue.inner_eval p beta MC MF v hp0 hp2 hp3 hq
    have hg' : ι gap = (SharingSeed15Degree124.shared31 p).evalRing (fun j => ι (v j)) := hg.trans he.symm
    refine ⟨Sign15Coordinate.lift v gap, ?_, Sign15ZeroBridge.forward p v gap hg' hz⟩
    simpa [Sign15Coordinate.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign15Coordinate.drop v, ?_, Sign15ZeroBridge.backward p v hz⟩
    simpa [Sign15Coordinate.drop] using hv
end DiophantineConsistency.Sign15SeedIff
#print axioms DiophantineConsistency.Sign15SeedIff.exists_same_input
