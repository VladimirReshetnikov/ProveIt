import DiophantineConsistency.Sign33StaticNode76
import DiophantineConsistency.Sign33ReferenceNode76
import DiophantineConsistency.Norm38ForwardGatesAssembly
import DiophantineConsistency.Norm38ForwardPrefix

/-! The natural negative representative reverses the 38 node76 ring value. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33NegativeNode76
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem negative_of_core (ports : Fin 4 → V) (u : Fin 14 → V) (negative : V)
    (hn : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι negative = d.y*d.y-d.V*d.V) :
    ι negative + pairValue ι (NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u) 76) = 0 := by
  let w := SharingForward38.witnessCoordinates ports u
  have hg : NormAssignment38.gatesHold ι ports w := Norm38ForwardGates.forward_gatesHold ι ports u
  have ht := Sign33StaticNode76.node76 ports w hg
  simp only [w, Norm38Forward.forward_prefix] at ht
  have hc := Sign33ReferenceNode76.reference76 (fun j => ι (ports j)) (fun j => ι (u j+1))
  have he := ht.trans hc
  dsimp only
  rw [he, hn]
  ring
end DiophantineConsistency.Sign33NegativeNode76
#print axioms DiophantineConsistency.Sign33NegativeNode76.negative_of_core
