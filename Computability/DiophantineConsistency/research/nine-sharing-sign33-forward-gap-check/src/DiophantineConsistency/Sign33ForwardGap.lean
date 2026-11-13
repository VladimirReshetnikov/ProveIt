import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly
import FreshModel106

/-! Gap representative to the first signed constructor equation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gap_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hgap : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι gap = (d.q-1)*(d.q-ι (u 1+1))+ι (u 2+1)) :
    let v := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 26) = (Sign33ResidualBatch04.t ports v*(Sign33ResidualBatch04.t ports v+1)+(ι (v 3)+1))-
      Sign33ResidualBatch04.t ports v*(ι (v 2)+1) := by
  simp [SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates,
    Sign33ResidualBatch04.t, map_add, map_mul]
  rw [hgap]
  simp [Carrier65.core, map_add, map_mul] <;> ring
end DiophantineConsistency.Sign33ForwardGap
#print axioms DiophantineConsistency.Sign33ForwardGap.gap_of_core
