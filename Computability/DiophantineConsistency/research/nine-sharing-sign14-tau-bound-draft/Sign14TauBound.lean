import DiophantineConsistency.Sign14TransportRow
import DiophantineConsistency.Sign14RankValue
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! SOURCE-ONLY nonnegative tau bound without a tau witness or N0 premise. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14TauBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign14SharedValues ArithmeticPellFirstIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rank_le_tau_head (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (SharingSeed14Degree124.seed p) v) :
    Sign14RankValue.Rank beta MC MF v ≤ E beta v * (v 10 + 1) + ((v 11 + 1) + (v 12 + 1)) := by
  have hpos (x : V) : 0 < x + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have ht := Sign14TransportRow.transport_of_seed p beta K v hp0 hp1 hz
  have hw := scalar_window (A beta v) beta K MC MF (v 1 + 1) (v 2 + 1)
    (v 3 + 1) (v 4 + 1) (v 9 + 1) (v 8 + 1)
    hb (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) hMC hMF rfl ht
  have hE : (v 9 + 1) * (v 8 + 1) * (A beta v)^4 = E beta v := by
    dsimp [E, Y]
    ring
  have hsmall : Sign14RankValue.Rank beta MC MF v + 2 < E beta v := by
    simpa only [Sign14RankValue.Rank, pow_two, hE] using hw.2.2
  have hr : Sign14RankValue.Rank beta MC MF v < E beta v :=
    lt_of_le_of_lt (by simp) hsmall
  have he : E beta v ≤ E beta v * (v 10 + 1) :=
    le_mul_of_one_le_right (by simp) (by simp)
  exact le_trans (le_of_lt hr) (le_trans he (by simp))

theorem tau_embedding (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (SharingSeed14Degree124.seed p) v) :
    ι (E beta v * (v 10 + 1) + ((v 11 + 1) + (v 12 + 1)) - Sign14RankValue.Rank beta MC MF v) =
      ι (E beta v * (v 10 + 1) + ((v 11 + 1) + (v 12 + 1))) - ι (Sign14RankValue.Rank beta MC MF v) := by
  rw [eq_sub_iff_add_eq, ← map_add, tsub_add_cancel_of_le (rank_le_tau_head p beta K MC MF v hp0 hp1 hb hMC hMF hz)]
end DiophantineConsistency.Sign14TauBound
#print axioms DiophantineConsistency.Sign14TauBound.rank_le_tau_head
#print axioms DiophantineConsistency.Sign14TauBound.tau_embedding
