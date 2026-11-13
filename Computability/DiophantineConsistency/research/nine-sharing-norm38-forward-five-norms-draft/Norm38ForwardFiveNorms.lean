import DiophantineConsistency.Norm38ReferenceTerminals
import DiophantineConsistency.Norm38ReferenceFieldsAll
import DiophantineConsistency.Norm38ForwardGatesAssembly
import DiophantineConsistency.Norm38ForwardPrefix

/-! UNCOMPILED draft: original unit norms imply five static targets for
 the generated witness. The terminal-reference provider is not yet checked. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardFiveNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forward_fiveNorms (ports : Fin 4 → V) (u : Fin 14 → V)
    (hu : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))
      d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1) :
    NormAssignment38.fiveNorms ι ports
      (SharingForward38.witnessCoordinates ports u) := by
  let w := SharingForward38.witnessCoordinates ports u
  have hg : NormAssignment38.gatesHold ι ports w :=
    Norm38ForwardGates.forward_gatesHold ι ports u
  have ht := Norm38Reference.static_terminals_agree ports w hg
  simp only [w, Norm38Forward.forward_prefix] at ht
  have hc := Norm38Reference.reference_terminal_fields_combined (fun j => ι (ports j))
    (fun j => ι (u j + 1))
  have hscale := Carrier65.strong_scale (fun j => ι (ports j)) (fun j => ι (u j + 1))
  rcases ht with ⟨ht0,ht1,hta,htt,hts,htd⟩
  rcases hc with ⟨hc0,hc1,hca,hct,hcs,hcd⟩
  rcases hu with ⟨hP,hQ,hU,hStrong,hW⟩
  have hZ : (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))).Z =
      (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))).delta := by
    rw [hscale,hStrong,mul_one]
  unfold NormAssignment38.fiveNorms
  exact ⟨ht0.trans (hc0.trans hP), ht1.trans (hc1.trans hQ),
    hta.trans (hca.trans hU), htt.trans (hct.trans hW),
    hts.trans (hcs.trans (hZ.trans (hcd.symm.trans htd.symm)))⟩
end DiophantineConsistency.Norm38ForwardFiveNorms
#print axioms DiophantineConsistency.Norm38ForwardFiveNorms.forward_fiveNorms
