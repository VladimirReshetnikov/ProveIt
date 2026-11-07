import DiophantineConsistency.Sign33ReferenceEll
import DiophantineConsistency.Norm38ReferenceTerminals
import DiophantineConsistency.Norm38ForwardGatesAssembly
import DiophantineConsistency.Norm38ForwardPrefix
import DiophantineConsistency.SharingForward33

/-! Topological binding of the constructor ell coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ConstructorEll
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ell_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 21) = (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))).ell := by
  let w := SharingForward38.witnessCoordinates ports u
  let val := fun j => pairValue ι (NormAssignment38.assignment ports w j)
  let ref := Norm38Reference.reference (fun j => ι (ports j))
    (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
  have hg : NormAssignment38.gatesHold ι ports w := Norm38ForwardGates.forward_gatesHold ι ports u
  have hfixed : val = ringRun NormAssignment38.gates val :=
    SharingTopology38.static_assignment_fixed ι ports w hg
  have hrun := SharingTopology38.ringRun_agrees_of_topological
    NormAssignment38.gates Norm38Reference.initialNodes val ref Norm38Reference.graph_topological
    (Norm38Reference.initial_agreement ports w) (Norm38Reference.reference_gate_equations_batched _ _)
  have heq : val 30 = ref 30 := (congrFun hfixed 30).trans (hrun 30 (by decide))
  have hc := Sign33ReferenceEll.reference_ell (fun j => ι (ports j)) (fun j => ι (u j+1))
  simp only [ref, w, Norm38Forward.forward_prefix] at heq
  have hvalue := heq.trans hc
  simp [val, w, NormAssignment38.assignment, pairValue] at hvalue
  have hcoord : (Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → V) 21 =
      SharingForward38.witnessCoordinates ports u 20 := by
    have hindex : (20 : Fin 33).succ = (21 : Fin 34) := by decide
    rw [←hindex, Fin.cons_succ]
    rfl
  dsimp only
  rw [hcoord]
  exact hvalue
end DiophantineConsistency.Sign33ConstructorEll
#print axioms DiophantineConsistency.Sign33ConstructorEll.ell_of_core
