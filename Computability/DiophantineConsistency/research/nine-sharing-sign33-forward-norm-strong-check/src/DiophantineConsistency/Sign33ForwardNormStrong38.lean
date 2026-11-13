import DiophantineConsistency.Norm38ReferenceTerminals
import DiophantineConsistency.Norm38ReferenceFieldsAll
import DiophantineConsistency.Norm38ForwardGatesAssembly
import DiophantineConsistency.Norm38ForwardPrefix

/-! Strong=1 gives the scaled 38-constructor terminal equality. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormStrong38
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem strong_terminal (ports : Fin 4 → V) (u : Fin 14 → V)
    (hs : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      Carrier65.strong d = 1) :
    pairValue ι (NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u) 80) =
      pairValue ι (NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u) 36) := by
  have hg := Norm38ForwardGates.forward_gatesHold ι ports u
  have ht := Norm38Reference.static_terminals_agree ports (SharingForward38.witnessCoordinates ports u) hg
  simp only [Norm38Forward.forward_prefix] at ht
  have hc := Norm38Reference.reference_terminal_fields_combined (fun j => ι (ports j)) (fun j => ι (u j+1))
  have hscale := Carrier65.strong_scale (fun j => ι (ports j)) (fun j => ι (u j+1))
  rcases ht with ⟨_,_,_,_,htz,htd⟩
  rcases hc with ⟨_,_,_,_,hcz,hcd⟩
  have hz : (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))).Z =
      (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))).delta := by
    rw [hscale,hs,mul_one]
  exact htz.trans (hcz.trans (hz.trans (hcd.symm.trans htd.symm)))
end DiophantineConsistency.Sign33ForwardNormStrong38
#print axioms DiophantineConsistency.Sign33ForwardNormStrong38.strong_terminal
