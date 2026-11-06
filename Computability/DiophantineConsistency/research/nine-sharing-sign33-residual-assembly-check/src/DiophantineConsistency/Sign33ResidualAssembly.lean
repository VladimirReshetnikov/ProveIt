import DiophantineConsistency.Sign33ResidualBatch00
import DiophantineConsistency.Sign33ResidualBatch01
import DiophantineConsistency.Sign33ResidualBatch02
import DiophantineConsistency.Sign33ResidualBatch03
import DiophantineConsistency.Sign33ResidualBatch04
import DiophantineConsistency.Sign33ResidualBatch05
import DiophantineConsistency.Sign33ResidualBatch06
import DiophantineConsistency.Sign33ResidualBatch07

/-! Same-valuation assembly of the eight checked sign33 residual batches. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure AllCuts (ports : Fin 4 → V) (v : Fin 34 → V) : Prop where
  batch00 :
    ι (v 15) = Sign33ResidualBatch00.q (ports 0) v*Sign33ResidualBatch00.q (ports 0) v ∧
        ι (v 16) = ι (v 15)*Sign33ResidualBatch00.q (ports 0) v ∧
        ι (v 17) = (ι (v 9)+1)*Sign33ResidualBatch00.q (ports 0) v
  batch01 :
    ι (v 18) = (ι (v 8)+1)*ι (v 16) ∧
        ι (v 19) = ι (v 17)*ι (v 18) ∧
        ι (v 20) = ((ι (v 11)+1)+(ι (v 12)+1))*ι (v 18)
  batch02 :
    ι (v 21) = ι (v 19)*ι (v 20) ∧
        ι (v 22) = (ι (v 19)+ι (v 18))*(ι (v 19)+ι (v 18))+(4*(ι (v 19)+ι (v 18))+3) ∧
        ι (v 23) = (ι (v 17)+((ι (v 19)+ι (v 18))*(ι (v 20)+(ι (v 11)+1))))+((ι (v 14)+1)*(4*(ι (v 19)+ι (v 18))+3))
  batch03 :
    ι (v 24) = (ι (v 20)+(ι (v 11)+1))*(ι (v 20)+(ι (v 11)+1)) ∧
        ι (v 25) = ι (v 22)*ι (v 24) ∧
        ι (v 23)*ι (v 23)-ι (v 25) = 1
  batch04 :
    ι (v 26) = (Sign33ResidualBatch04.t ports v*(Sign33ResidualBatch04.t ports v+1)+(ι (v 3)+1))-Sign33ResidualBatch04.t ports v*(ι (v 2)+1) ∧
        ι (v 27) = ((ι (v 19)*(ι (v 10)+1)+((ι (v 11)+1)+(ι (v 12)+1)))+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+Sign33ResidualBatch04.q ports v*ι (ports 3))*(ι (v 1)+1)) ∧
        ι (v 27)*ι (v 27)-ι (v 21)*(ι (v 21)+((ι (v 11)+1)+(ι (v 12)+1))) = 1
  batch05 :
    (((ι (ports 1)+(ι (v 9)+1))*Sign33ResidualBatch05.q ports v)+Sign33ResidualBatch05.q ports v)-((((ι (ports 1)+(ι (v 9)+1))*((ι (v 2)+1)+(ι (v 3)+1)))+(ι (v 2)+1))+((ι (v 4)+1)*Sign33ResidualBatch05.t ports v)) = 1 ∧
        ι (v 28) = (ι (v 5)+1)*(ι (v 5)+1) ∧
        ι (v 29) = ((ι (v 20)+(ι (v 11)+1))*(ι (v 7)+1)+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+Sign33ResidualBatch05.q ports v*ι (ports 3))*(ι (v 1)+1))
  batch06 :
    ι (v 30) = ι (v 28)*ι (v 29)-(ι (v 20)+(ι (v 11)+1)) ∧
        ι (v 31) = (ι (v 6)+1)*ι (v 25) ∧
        ι (v 32) = ι (v 31)*ι (v 31)
  batch07 :
    ι (v 33) = (ι (v 13)+1)*(ι (v 13)+1)-ι (v 30)*ι (v 30) ∧
        (ι (v 13)+1)*(ι (v 13)+1)-ι (v 32)*ι (v 33) = 1 ∧
        ι (v 22)*ι (v 28)-ι (v 32) = ι (v 22)

theorem all_cuts_of_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3))
    (hz : InternalZero (SharingSeed33.seed p) v) : AllCuts ports v := by
  exact ⟨
    Sign33ResidualBatch00.three_cuts_of_seed_zero p ports v hp0 hz,
    Sign33ResidualBatch01.three_cuts_of_seed_zero p v hz,
    Sign33ResidualBatch02.three_cuts_of_seed_zero p v hz,
    Sign33ResidualBatch03.two_cuts_and_norm_of_seed_zero p v hz,
    Sign33ResidualBatch04.signed_cuts_and_norm_of_seed_zero p ports v hp0 hp2 hp3 hz,
    Sign33ResidualBatch05.transport_and_cuts_of_seed_zero p ports v hp0 hp1 hp2 hp3 hz,
    Sign33ResidualBatch06.three_cuts_of_seed_zero p v hz,
    Sign33ResidualBatch07.cut_and_norms_of_seed_zero p v hz⟩
end DiophantineConsistency.Sign33ResidualAssembly
#print axioms DiophantineConsistency.Sign33ResidualAssembly.all_cuts_of_seed_zero
