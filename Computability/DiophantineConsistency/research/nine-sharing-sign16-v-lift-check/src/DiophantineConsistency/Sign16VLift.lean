import DiophantineConsistency.Sign16WindowAssembly
import DiophantineConsistency.Sign33InnerVRing

/-! SOURCE-ONLY natural representative for the deleted sign16 V coordinate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16VLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
open ArithmeticPellRecurrence
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_v_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 17 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (seed p) v) :
    ∃ gap : V, ι gap = (ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - ι (C beta v) := by
  have hpos (x : V) : 0 < x + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hc : 0 < C beta v := by
    unfold C
    exact lt_of_lt_of_le (hpos (v 11)) le_add_self
  have hh := Sign16WindowAssembly.half_window_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
  have hs := Sign16StrictNorm.strict_of_seed p beta v hp0 hz
  have hs' : (v 5 + 1) * (v 5 + 1) =
      1 + delta (E beta v + Y beta v) * ((v 6 + 1) * C beta v * C beta v) *
        ((v 6 + 1) * C beta v * C beta v) := by
    simpa only [delta] using hs
  have hv := Sign33InnerVRing.inner_v_of_window_and_strong (E beta v + Y beta v)
    (C beta v) (v 7 + 1) (Sign16RankValue.Rank beta MC MF v) (v 5 + 1) (v 6 + 1)
    hc (hpos _) (hpos _) (hpos _) hh hs'
  have hi := Sign16InnerFromSeed.inner_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
  apply nonneg_iff.mp
  simp only [map_add, map_one] at hi
  rw [hi]
  exact hv.2
end DiophantineConsistency.Sign16VLift
#print axioms DiophantineConsistency.Sign16VLift.exists_v_of_seed
