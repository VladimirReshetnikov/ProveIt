import DiophantineConsistency.Sign14TransportRow
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! SOURCE-ONLY scalar window from retained Nt and explicit port bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14ScalarWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign14SharedValues ArithmeticPellFirstIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem q_bound_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (SharingSeed14Degree124.seed p) v) :
    v 2 + 1 ≤ A beta v := by
  have hpos (x : V) : 0 < x + 1 := lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have ht := Sign14TransportRow.transport_of_seed p beta K v hp0 hp1 hz
  have hw := scalar_window (A beta v) beta K MC MF (v 1 + 1) (v 2 + 1)
    (v 3 + 1) (v 4 + 1) (v 9 + 1) (v 8 + 1)
    hb (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) (hpos _) hMC hMF rfl ht
  have hqF : 0 < A beta v - (v 2 + 1) :=
    lt_of_le_of_lt (show (0 : V) ≤ v 3 + 1 from zero_le) (tsub_pos_iff_lt.mp hw.1)
  exact le_of_lt (tsub_pos_iff_lt.mp hqF)
end DiophantineConsistency.Sign14ScalarWindow
#print axioms DiophantineConsistency.Sign14ScalarWindow.q_bound_of_seed
