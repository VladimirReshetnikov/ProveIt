import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly
import FreshModel106

/-! Conditional Q-unit norm to the constructor Q field; source-only draft. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormQ
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_q_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hq : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      d.Q = 1) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 23)*ι (v 23)-ι (v 25) = 1 := by
  simp [SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates, map_add, map_mul]
  simp [Carrier65.core, map_add, map_mul, pow_succ] at hq
  convert hq using 1 <;> ring
end DiophantineConsistency.Sign33ForwardNormQ
#print axioms DiophantineConsistency.Sign33ForwardNormQ.norm_q_of_core
