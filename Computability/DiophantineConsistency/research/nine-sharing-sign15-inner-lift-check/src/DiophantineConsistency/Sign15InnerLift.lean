import DiophantineConsistency.Sign15WindowAssembly
import DiophantineConsistency.Sign33InnerVRing

/-! SOURCE-ONLY natural representative for the deleted sign15 V coordinate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15InnerLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed15Degree124 Sign15SharedValues
open ArithmeticPellRecurrence
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_inner_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 16 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (seed p) v) :
    ∃ gap : V, ι gap = ι (C beta v) * ι (v 7 + 1) - ι (Sign15RankValue.Rank beta MC MF v) := by
  have hpos (x : V) : 0 < x + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hc : 0 < C beta v := by
    unfold C
    exact lt_of_lt_of_le (hpos (v 11)) le_add_self
  have hh := Sign15WindowAssembly.half_window_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
  have hs := Sign15StrictNorm.strict_of_seed p beta v hp0 hz
  have hs' : (v 5 + 1) * (v 5 + 1) =
      1 + delta (E beta v + Y beta v) * ((v 6 + 1) * C beta v * C beta v) *
        ((v 6 + 1) * C beta v * C beta v) := by
    simpa only [delta] using hs
  have hv := Sign33InnerVRing.inner_v_of_window_and_strong (E beta v + Y beta v)
    (C beta v) (v 7 + 1) (Sign15RankValue.Rank beta MC MF v) (v 5 + 1) (v 6 + 1)
    hc (hpos _) (hpos _) (hpos _) hh hs'
  obtain ⟨gap, hgap⟩ := nonneg_iff.mp hv.1
  exact ⟨gap, hgap.symm⟩
end DiophantineConsistency.Sign15InnerLift
#print axioms DiophantineConsistency.Sign15InnerLift.exists_inner_of_seed
