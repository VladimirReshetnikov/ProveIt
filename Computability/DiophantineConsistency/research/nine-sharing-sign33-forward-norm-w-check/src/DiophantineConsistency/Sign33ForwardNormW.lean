import DiophantineConsistency.Sign33ForwardNormW38
import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly

/-! W transport to the 33-constructor W field. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormW
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_w_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hw : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      d.W = 1) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    (((ι (ports 1)+(ι (v 9)+1))*Sign33ResidualBatch05.q ports v)+Sign33ResidualBatch05.q ports v)-((((ι (ports 1)+(ι (v 9)+1))*((ι (v 2)+1)+(ι (v 3)+1)))+(ι (v 2)+1))+((ι (v 4)+1)*Sign33ResidualBatch05.t ports v)) = 1 := by
  have ht := Sign33ForwardNormW38.w_terminal ports u hw
  simp [NormAssignment38.assignment, pairValue, pairCompute,
    SharingForward38.witnessCoordinates, map_add, map_mul] at ht
  simp [SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates,
    Sign33ResidualBatch05.q, Sign33ResidualBatch05.t, map_add, map_mul]
  convert ht using 1 <;> ring
end DiophantineConsistency.Sign33ForwardNormW
#print axioms DiophantineConsistency.Sign33ForwardNormW.norm_w_of_core
