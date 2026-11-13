import DiophantineConsistency.Norm38StaticCarrierCompose
import FreshModel106

/-! Proposed generic-port translation from static constraints to source zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem static_implies_source_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hg : NormAssignment38.gatesHold ι ports w)
    (hn : NormAssignment38.fiveNorms ι ports w) :
    InternalZero (ObjectCurrentEquation2011.expressionAt p)
      (fun j => w (Fin.castLE (by decide : 14 ≤ 38) j) + 1) := by
  rw [internalZero_iff, FreshModel106.evalRing_expressionAt65]
  simpa only [hp] using static_gates_norms_imply_value ports w hg hn

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.static_implies_source_zero
