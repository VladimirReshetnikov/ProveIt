import DirectBFSSymbolicKernel
import DiophantineConsistency.Compact943Data

/-! Both finite tile tables use the advertised typed-color domains. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace DirectBFSColorBounds

def inDomains (t : Nat × Nat × Nat × Nat) : Bool :=
  decide (t.1<250 ∧ t.2.1<439 ∧ t.2.2.1<250 ∧ t.2.2.2<439)

theorem original_colors : Compact943Data.rows.all inDomains = true := by decide

theorem direct_colors : DirectBFSSymbolicKernel.rows.all inDomains = true := by decide

#print axioms DirectBFSColorBounds.original_colors
#print axioms DirectBFSColorBounds.direct_colors
end DirectBFSColorBounds
