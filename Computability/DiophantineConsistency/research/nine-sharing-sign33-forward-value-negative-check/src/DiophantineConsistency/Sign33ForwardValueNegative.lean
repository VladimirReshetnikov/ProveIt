import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly
import FreshModel106

/-! Conditional value and negative constructor cuts, source-only draft. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardValueNegative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem value_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hinner : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι inner = d.c * ι (u 6+1) - d.rank)
    (hvalue : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι value = d.V) :
    let v := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 30) = ι (v 28)*ι (v 29)-(ι (v 20)+(ι (v 11)+1)) := by
  simp [SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates, map_add, map_mul]
  rw [hvalue, hinner]
  simp [Carrier65.core, map_add, map_mul, pow_succ] <;> ring

theorem negative_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hvalue : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι value = d.V)
    (hnegative : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι negative = d.y*d.y-d.V*d.V) :
    let v := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 33) = (ι (v 13)+1)*(ι (v 13)+1)-ι (v 30)*ι (v 30) := by
  simp [SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates, map_add, map_mul]
  rw [hnegative, hvalue]
  simp [Carrier65.core, map_add, map_mul, pow_succ] <;> ring
end DiophantineConsistency.Sign33ForwardValueNegative
#print axioms DiophantineConsistency.Sign33ForwardValueNegative.value_of_core
#print axioms DiophantineConsistency.Sign33ForwardValueNegative.negative_of_core
