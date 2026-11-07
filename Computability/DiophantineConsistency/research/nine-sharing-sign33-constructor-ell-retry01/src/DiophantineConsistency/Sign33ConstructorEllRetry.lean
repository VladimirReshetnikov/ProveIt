import DiophantineConsistency.Sign33StaticNode30
import DiophantineConsistency.Sign33ReferenceEll
import DiophantineConsistency.Norm38ForwardGatesAssembly
import DiophantineConsistency.Norm38ForwardPrefix
import DiophantineConsistency.Sign33AbstractProjection21

/-! Constructor ell via separately checked topology and abstract coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ConstructorEllRetry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ell_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 21) = (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))).ell := by
  let w := SharingForward38.witnessCoordinates ports u
  have hg : NormAssignment38.gatesHold ι ports w := Norm38ForwardGates.forward_gatesHold ι ports u
  have ht := Sign33StaticNode30.node30 ports w hg
  simp only [w, Norm38Forward.forward_prefix] at ht
  have hc := Sign33ReferenceEll.reference_ell (fun j => ι (ports j)) (fun j => ι (u j+1))
  have he := ht.trans hc
  simp [w, NormAssignment38.assignment, pairValue] at he
  dsimp only
  rw [Sign33AbstractProjection21.project]
  exact he
end DiophantineConsistency.Sign33ConstructorEllRetry
#print axioms DiophantineConsistency.Sign33ConstructorEllRetry.ell_of_core
