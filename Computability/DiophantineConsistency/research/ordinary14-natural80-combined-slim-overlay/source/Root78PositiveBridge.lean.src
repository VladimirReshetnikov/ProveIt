import Compact78To88
import Quotient88PositiveBridge

/-! Source-only proposed 78-graph positive-model bridge. The graph comparisons,
quotient bridge and all transitive imports remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Root78PositiveBridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open IPRAOrdinary12 (PositiveModelBridge)
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) := (P78AuxRoot.graph CompactSymbolicModelIff.p).output

/-- Proposed positive-model bridge through the same symbolic-port 78↔88
comparison and the proposed quotient-88 positive bridge. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  have hpair := Compact78To88Draft.positive_zero_iff (V:=V) (paramKernel rho)
  change (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧ InternalZero expression v) ↔
    (∃ w : Fin 14 → V, (∀ j, 0<w j) ∧ InternalZero Quotient88PositiveBridgeDraft.expression w) at hpair
  exact hpair.trans (Quotient88PositiveBridgeDraft.positiveBridge V)

end DiophantineConsistency.Root78PositiveBridgeDraft

#print axioms DiophantineConsistency.Root78PositiveBridgeDraft.positiveBridge
