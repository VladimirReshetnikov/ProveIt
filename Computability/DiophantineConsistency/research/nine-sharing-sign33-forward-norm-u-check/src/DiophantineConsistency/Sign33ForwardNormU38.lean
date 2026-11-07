import DiophantineConsistency.Norm38ReferenceTerminals
import DiophantineConsistency.Norm38ReferenceFieldsAll
import DiophantineConsistency.Norm38ForwardGatesAssembly
import DiophantineConsistency.Norm38ForwardPrefix

/-! U core unit implies the U static terminal for the 38 constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormU38
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem u_terminal (ports : Fin 4 → V) (u : Fin 14 → V)
    (hu : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      d.U = 1) :
    pairValue ι (NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u) 78) = 1 := by
  have hg := Norm38ForwardGates.forward_gatesHold ι ports u
  have ht := Norm38Reference.static_terminals_agree ports (SharingForward38.witnessCoordinates ports u) hg
  simp only [Norm38Forward.forward_prefix] at ht
  have hc := Norm38Reference.reference_terminal_fields_combined (fun j => ι (ports j)) (fun j => ι (u j+1))
  exact ht.2.2.1.trans (hc.2.2.1.trans hu)
end DiophantineConsistency.Sign33ForwardNormU38
#print axioms DiophantineConsistency.Sign33ForwardNormU38.u_terminal
