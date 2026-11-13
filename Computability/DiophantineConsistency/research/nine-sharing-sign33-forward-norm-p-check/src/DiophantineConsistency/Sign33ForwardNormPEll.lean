import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly
import FreshModel106

/-! Constructor ell coordinate compared with the shifted source core. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormPEll
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ell_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 21) = (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))).ell := by
  simp [SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates,
    Carrier65.core, map_add, map_mul, pow_succ] <;> ring
end DiophantineConsistency.Sign33ForwardNormPEll
#print axioms DiophantineConsistency.Sign33ForwardNormPEll.ell_of_core
