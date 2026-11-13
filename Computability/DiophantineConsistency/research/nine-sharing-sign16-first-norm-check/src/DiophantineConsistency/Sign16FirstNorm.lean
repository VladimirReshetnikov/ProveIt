import DiophantineConsistency.Sign16InnerFromSeed
import DiophantineConsistency.Sign16OtherRows
import DiophantineConsistency.Sign16MoreSharedValues

/-! SOURCE-ONLY first maintained norm, using retained natural tau. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16FirstNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 17 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (seed p) v) :
    let k := (v 11 + 1) + (v 12 + 1)
    let r := Sign16RankValue.Rank beta MC MF v
    let tau := E beta v * (v 10 + 1) + k - r
    tau*tau = 1 + (E beta v * Y beta v) * (E beta v * Y beta v + 1) * k*k := by
  dsimp only
  have hq := Sign16ScalarWindow.q_bound_of_seed p beta K MC MF v hp0 hp1 hb hMC hMF hz
  have hrank := Sign16RankValue.rank_eval p beta MC MF v hp0 hp2 hp3 hq
  have hrow := Sign16OtherRows.row01_of_seed p v hz
  change ι (v 15) - ((shared19 p).evalRing (fun i => ι (v i)) * (ι (v 10) + 1) +
    ((ι (v 11) + 1) + (ι (v 12) + 1)) + (shared15 p).evalRing (fun i => ι (v i)) -
    (shared25 p).evalRing (fun i => ι (v i))) = 0 at hrow
  rw [Sign16MoreSharedValues.e_eval p beta v hp0] at hrow
  have htau : v 15 + Sign16RankValue.Rank beta MC MF v =
      E beta v * (v 10 + 1) + ((v 11 + 1) + (v 12 + 1)) := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    linarith only [hrow, hrank]
  have ht : E beta v * (v 10 + 1) + ((v 11 + 1) + (v 12 + 1)) -
      Sign16RankValue.Rank beta MC MF v = v 15 := by
    rw [← htau, add_tsub_cancel_right]
  rw [ht]
  have hrow2 := Sign16OtherRows.row02_of_seed p v hz
  change ι (v 15) * ι (v 15) - (shared27 p).evalRing (fun i => ι (v i)) *
    ((shared27 p).evalRing (fun i => ι (v i)) + ((ι (v 11) + 1) + (ι (v 12) + 1))) - 1 = 0 at hrow2
  rw [Sign16MoreSharedValues.ey_k_eval p beta v hp0] at hrow2
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  apply sub_eq_zero.mp
  calc
    _ = ι (v 15) * ι (v 15) -
      ι (E beta v * (((v 11 + 1) + (v 12 + 1)) * Y beta v)) *
      (ι (E beta v * (((v 11 + 1) + (v 12 + 1)) * Y beta v)) +
        ((ι (v 11) + 1) + (ι (v 12) + 1))) - 1 := by
          simp only [map_add, map_mul, map_one]
          ring
    _ = 0 := hrow2
end DiophantineConsistency.Sign16FirstNorm
#print axioms DiophantineConsistency.Sign16FirstNorm.first_of_seed
