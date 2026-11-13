import DiophantineConsistency.Sign33ForwardNormQ38
import DiophantineConsistency.SharingForward33

/-! The 33 constructor shares the two positive coordinates needed by Q. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormQRetry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_q_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hq : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      d.Q = 1) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 23)*ι (v 23)-ι (v 25) = 1 := by
  have ht := Sign33ForwardNormQ38.q_terminal ports u hq
  have hs : pairValue ι (NormAssignment38.assignment ports
      (SharingForward38.witnessCoordinates ports u) 44) =
      ι (SharingForward38.witnessCoordinates ports u 22) *
        ι (SharingForward38.witnessCoordinates ports u 22) -
        ι (SharingForward38.witnessCoordinates ports u 24) := by
    simp [NormAssignment38.assignment, pairValue, pairCompute, map_add, map_mul]
  rw [hs] at ht
  change ι (SharingForward38.witnessCoordinates ports u 22) *
    ι (SharingForward38.witnessCoordinates ports u 22) -
    ι (SharingForward38.witnessCoordinates ports u 24) = 1
  exact ht
end DiophantineConsistency.Sign33ForwardNormQRetry
#print axioms DiophantineConsistency.Sign33ForwardNormQRetry.norm_q_of_core
