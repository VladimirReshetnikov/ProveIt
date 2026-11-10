import DiophantineConsistency.Sign16ScalarWindow
import DiophantineConsistency.Sign16RankValue
import DiophantineConsistency.Sign16RowPremises

/-! SOURCE-ONLY: natural rank and inner equation from a sign16 seed zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16InnerFromSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem inner_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 17 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (seed p) v) :
    ι (v 16) = ι (C beta v) * ι (v 7 + 1) - ι (Sign16RankValue.Rank beta MC MF v) := by
  have hq := Sign16ScalarWindow.q_bound_of_seed p beta K MC MF v hp0 hp1 hb hMC hMF hz
  have hr := Sign16RankValue.rank_eval p beta MC MF v hp0 hp2 hp3 hq
  have hc := Sign16SharedValues.c_eval p beta v hp0
  have hi := Sign16RowPremises.inner_of_seed p v hz
  change ι (v 16) = (shared18 p).evalRing (fun i => ι (v i)) * (ι (v 7) + 1) +
    (shared15 p).evalRing (fun i => ι (v i)) -
    (shared25 p).evalRing (fun i => ι (v i)) at hi
  rw [hc] at hi
  simp only [map_add, map_one]
  linarith only [hi, hr]
end DiophantineConsistency.Sign16InnerFromSeed
#print axioms DiophantineConsistency.Sign16InnerFromSeed.inner_of_seed
