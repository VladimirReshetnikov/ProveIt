import Model78To74
import Root78PositiveBridge
import CompactPortBoundsSlim

/-! Source-only proposed positive-model bridge for the 74 graph. All graph,
comparison and inherited endpoint imports remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Root74PositiveBridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open IPRAOrdinary12 (PositiveModelBridge)
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) := (P74PositiveGuard.graph CompactSymbolicModelIff.p).output

/-- Proposed positive bridge at the existing symbolic compact port tuple. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  let p : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  have hb := CompactPortBoundsSlimDraft.port_bounds (V:=V) CompactFixedBeta.betaNat
    (paramKernel rho) lowNat highNat CompactFixedBeta.beta_identity rfl rfl
  have hpair := Model78To74Draft.positive_zero_iff_natural_ports (V:=V) p hb.1
  change (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero Root78PositiveBridgeDraft.expression v) ↔
    (∃ w : Fin 14 → V, (∀ j, 0<w j) ∧ InternalZero expression w) at hpair
  exact hpair.symm.trans (Root78PositiveBridgeDraft.positiveBridge V)

end DiophantineConsistency.Root74PositiveBridgeDraft

#print axioms DiophantineConsistency.Root74PositiveBridgeDraft.positiveBridge
