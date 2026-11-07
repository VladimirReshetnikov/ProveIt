import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly
import FreshModel106

/-! Gap and tau representatives to the signed tau constructor equation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardTau
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem tau_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hgap : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι gap = (d.q-1)*(d.q-ι (u 1+1))+ι (u 2+1))
    (htau : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι tau = d.tau) :
    let v := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 27) = ((ι (v 19)*(ι (v 10)+1)+((ι (v 11)+1)+(ι (v 12)+1)))+ι (v 26))-
      (ι (v 26)*ι (v 15)+(ι (ports 2)+Sign33ResidualBatch04.q ports v*ι (ports 3))*(ι (v 1)+1)) := by
  simp [SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates,
    Sign33ResidualBatch04.q, Sign33ResidualBatch04.t, map_add, map_mul]
  rw [htau, hgap]
  simp [Carrier65.core, map_add, map_mul, pow_succ] <;> ring
end DiophantineConsistency.Sign33ForwardTau
#print axioms DiophantineConsistency.Sign33ForwardTau.tau_of_core
