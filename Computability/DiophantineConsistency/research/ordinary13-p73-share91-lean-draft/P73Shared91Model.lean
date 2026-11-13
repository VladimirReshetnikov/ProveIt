import P73Shared91
import DiophantineConsistency.Compact44.IPRAPositive73

/-! Uncompiled model transfer; the checked P73 provider is a separate input. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P73Shared91Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open IPRAOrdinary12 (PositiveModelBridge)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 13) :=
  (P73Shared91.graph91 (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (P73Shared91.graph91 p).output v ↔
      InternalZero (P73Graph.graph p).output v := by
  rw [internalZero_iff, internalZero_iff, P73Shared91.eval_eq]

theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  refine Iff.trans ?_ (IPRAPositive73.positiveBridge V)
  constructor
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, hv, (zero_iff _ v).1 hz⟩
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, hv, (zero_iff _ v).2 hz⟩

end DiophantineConsistency.P73Shared91Model

#print axioms DiophantineConsistency.P73Shared91Model.zero_iff
#print axioms DiophantineConsistency.P73Shared91Model.positiveBridge
