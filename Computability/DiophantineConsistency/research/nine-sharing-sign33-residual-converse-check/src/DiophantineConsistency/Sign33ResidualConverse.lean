import DiophantineConsistency.Sign33ResidualConverse00
import DiophantineConsistency.Sign33ResidualConverse01
import DiophantineConsistency.Sign33ResidualConverse02
import DiophantineConsistency.Sign33ResidualConverse03
import DiophantineConsistency.Sign33ResidualConverse04
import DiophantineConsistency.Sign33ResidualConverse05
import DiophantineConsistency.Sign33ResidualConverse06
import DiophantineConsistency.Sign33ResidualConverse07

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_of_all_cuts (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3))
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    InternalZero (SharingSeed33.seed p) v := by
  have hg0 := Sign33ResidualConverse00.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  have hg1 := Sign33ResidualConverse01.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  have hg2 := Sign33ResidualConverse02.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  have hg3 := Sign33ResidualConverse03.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  have hg4 := Sign33ResidualConverse04.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  have hg5 := Sign33ResidualConverse05.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  have hg6 := Sign33ResidualConverse06.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  have hg7 := Sign33ResidualConverse07.residuals_zero p ports v hp0 hp1 hp2 hp3 hc
  apply (SharingSign33Squares.seed_zero_iff_residuals p v).mpr
  intro r hr
  simp only [SharingSeed33.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg0.1
  · simpa only [Sign33ResidualBatch00.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg0.2.1
  · simpa only [Sign33ResidualBatch00.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg0.2.2
  · simpa only [Sign33ResidualBatch01.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg1.1
  · simpa only [Sign33ResidualBatch01.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg1.2.1
  · simpa only [Sign33ResidualBatch01.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg1.2.2
  · simpa only [Sign33ResidualBatch02.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg2.1
  · simpa only [Sign33ResidualBatch02.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg2.2.1
  · simpa only [Sign33ResidualBatch02.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg2.2.2
  · simpa only [Sign33ResidualBatch03.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg3.1
  · simpa only [Sign33ResidualBatch03.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg3.2.1
  · simpa only [Sign33ResidualBatch03.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg3.2.2
  · simpa only [Sign33ResidualBatch04.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg4.1
  · simpa only [Sign33ResidualBatch04.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg4.2.1
  · simpa only [Sign33ResidualBatch04.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg4.2.2
  · simpa only [Sign33ResidualBatch05.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg5.1
  · simpa only [Sign33ResidualBatch05.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg5.2.1
  · simpa only [Sign33ResidualBatch05.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg5.2.2
  · simpa only [Sign33ResidualBatch06.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg6.1
  · simpa only [Sign33ResidualBatch06.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg6.2.1
  · simpa only [Sign33ResidualBatch06.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg6.2.2
  · simpa only [Sign33ResidualBatch07.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg7.1
  · simpa only [Sign33ResidualBatch07.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg7.2.1
  · simpa only [Sign33ResidualBatch07.tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ, List.getD_cons_zero] using hg7.2.2
end DiophantineConsistency.Sign33ResidualConverse
#print axioms DiophantineConsistency.Sign33ResidualConverse.seed_zero_of_all_cuts
