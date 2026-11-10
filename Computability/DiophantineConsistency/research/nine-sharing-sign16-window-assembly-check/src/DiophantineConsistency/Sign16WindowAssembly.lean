import DiophantineConsistency.Sign16FirstNorm
import DiophantineConsistency.Sign16StrictNorm
import DiophantineConsistency.Sign16AuxFromSeed
import DiophantineConsistency.Sign16WindowScale
import DiophantineConsistency.Sign33Windows

/-! SOURCE-ONLY assembly of maintained norms into the sign16 half-window. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign16WindowAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
open ArithmeticPellRecurrence
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem half_window_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 17 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (seed p) v) :
    2 * Sign16RankValue.Rank beta MC MF v < C beta v := by
  have hpos (x : V) : 0 < x + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hq : beta * (v 1 + 1) + 1 = A beta v := rfl
  have hY : (v 8 + 1) * (A beta v)^3 = Y beta v := by
    simp only [Y, pow_succ, pow_zero, mul_one]
    ring
  have hE : (v 9 + 1) * A beta v * Y beta v = E beta v := rfl
  have hc : ((v 11 + 1) + (v 12 + 1)) * Y beta v + (v 11 + 1) = C beta v := rfl
  have hR : ((A beta v - 1) * (A beta v - (v 2 + 1)) + (v 3 + 1)) *
      ((A beta v)^2 - 1) + (MC + A beta v * MF) * (v 1 + 1) =
      Sign16RankValue.Rank beta MC MF v := by
    simp only [Sign16RankValue.Rank, pow_two]
  have hd : (v 9 + 1) * A beta v + (E beta v + Y beta v) * C beta v +
      (v 14 + 1) * (4 * (E beta v + Y beta v) + 3) = Root beta v + 1 := by
    dsimp [Root, B, Tail, E, A]
    ring
  have hscale : delta (E beta v + Y beta v) * (v 6 + 1) * C beta v * C beta v = Scale beta v := by
    rw [Sign16WindowScale.scale_of_seed p beta v hp0 hz]
    dsimp [delta]
    ring
  have ht := Sign16TransportRow.transport_of_seed p beta K v hp0 hp1 hz
  have hf := Sign16FirstNorm.first_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
  have hm := Sign16MainNorm.main_of_seed p beta v hp0 hz
  have hs := Sign16StrictNorm.strict_of_seed p beta v hp0 hz
  have ha := Sign16AuxFromSeed.auxiliary_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
  have hw := Sign33Windows.windows_from_maintained_norms beta K MC MF
    (v 1 + 1) (v 2 + 1) (v 3 + 1) (v 4 + 1) (v 5 + 1) (v 6 + 1)
    (v 7 + 1) (v 8 + 1) (v 9 + 1) (v 10 + 1) (v 11 + 1) (v 12 + 1)
    (v 13 + 1) (v 14 + 1) hb hMC hMF
    (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hpos _)
    (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hpos _)
  dsimp only at hw hf hm hs ha
  simp only [hq, hY, hE, hc, hR, hd, hscale] at hw
  have hm' : (Root beta v + 1) * (Root beta v + 1) =
      1 + delta (E beta v + Y beta v) * C beta v * C beta v := by
    simpa only [delta] using hm
  have hs' : (v 5 + 1) * (v 5 + 1) =
      1 + delta (E beta v + Y beta v) * ((v 6 + 1) * C beta v * C beta v) *
        ((v 6 + 1) * C beta v * C beta v) := by
    simpa only [delta] using hs
  exact (hw ht hf hm' hs' ha).2.2
end DiophantineConsistency.Sign16WindowAssembly
#print axioms DiophantineConsistency.Sign16WindowAssembly.half_window_of_seed
