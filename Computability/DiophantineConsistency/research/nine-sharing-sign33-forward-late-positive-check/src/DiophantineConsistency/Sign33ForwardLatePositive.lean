import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly

/-! f-squared and normalized S/S-squared cut equations for the candidate forward constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardLatePositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def condition (v : Fin 34 → V) : Prop :=
  ι (v 28) = (ι (v 5)+1)*(ι (v 5)+1) ∧
  ι (v 31) = (ι (v 6)+1)*ι (v 25) ∧
  ι (v 32) = ι (v 31)*ι (v 31)

theorem constructor_cuts (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V) :
    condition (Fin.cons (1 : V)
      (SharingForward33.witnessCoordinates ports u gap tau inner value negative)) := by
  simp [condition, SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates,
    map_add, map_mul, map_ofNat]
end DiophantineConsistency.Sign33ForwardLatePositive
#print axioms DiophantineConsistency.Sign33ForwardLatePositive.constructor_cuts
