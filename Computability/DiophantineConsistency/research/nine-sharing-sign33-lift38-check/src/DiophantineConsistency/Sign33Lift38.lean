import DiophantineConsistency.Sign33ResidualAssembly

/-! Source-only candidate: signed cuts and zero-padded lift to 38 witnesses. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33Lift38
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def signedValues (v : Fin 34 → V) : Fin 5 → DiffRing V :=
  ![ι (v 26), ι (v 27), ι (v 29), ι (v 30), ι (v 33)]

def lift (v : Fin 34 → V) : Fin 38 → V :=
  ![v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, 0, v 27, 0, v 28, v 29, 0, v 30, 0, v 31, v 32, 0, v 33]

theorem signed_values_of_all_cuts (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    signedValues v 0 = (Sign33ResidualBatch04.t ports v*(Sign33ResidualBatch04.t ports v+1)+(ι (v 3)+1))-Sign33ResidualBatch04.t ports v*(ι (v 2)+1) ∧
    signedValues v 1 = ((ι (v 19)*(ι (v 10)+1)+((ι (v 11)+1)+(ι (v 12)+1)))+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+Sign33ResidualBatch04.q ports v*ι (ports 3))*(ι (v 1)+1)) ∧
    signedValues v 2 = ((ι (v 20)+(ι (v 11)+1))*(ι (v 7)+1)+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+Sign33ResidualBatch05.q ports v*ι (ports 3))*(ι (v 1)+1)) ∧
    signedValues v 3 = ι (v 28)*ι (v 29)-(ι (v 20)+(ι (v 11)+1)) ∧
    signedValues v 4 = (ι (v 13)+1)*(ι (v 13)+1)-ι (v 30)*ι (v 30) := by
  exact ⟨hc.batch04.1, hc.batch04.2.1, hc.batch05.2.2,
    hc.batch06.1, hc.batch07.1⟩

theorem lift_inputs (v : Fin 34 → V) (i : Fin 14) :
    lift v (Fin.castLE (by decide : 14 ≤ 38) i) = v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ i)) := by
  fin_cases i <;> rfl

theorem lift_signed_coordinates (v : Fin 34 → V) :
    lift v 25 = v 26 ∧ lift v 26 = 0 ∧
    lift v 27 = v 27 ∧ lift v 28 = 0 ∧
    lift v 30 = v 29 ∧ lift v 31 = 0 ∧
    lift v 32 = v 30 ∧ lift v 33 = 0 ∧
    lift v 36 = 0 ∧ lift v 37 = v 33 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end DiophantineConsistency.Sign33Lift38
#print axioms DiophantineConsistency.Sign33Lift38.signed_values_of_all_cuts
#print axioms DiophantineConsistency.Sign33Lift38.lift_inputs
#print axioms DiophantineConsistency.Sign33Lift38.lift_signed_coordinates
