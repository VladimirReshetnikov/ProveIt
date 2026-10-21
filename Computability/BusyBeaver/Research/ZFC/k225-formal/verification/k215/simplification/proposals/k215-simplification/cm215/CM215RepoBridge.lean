import BusyBeaver.ZFC.KDense215
import CM215CoreBridge

/-! Exact formal attachment to the repository's published K215 `Machine 215`.
This file needs the pinned repository's KDense215 build, but no ZFC endpoint
imports. The complete theorem transfers any already established calibration. -/
namespace CM215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All 430 original rows agree in the actual repository's machine type. -/
theorem parent_rows : ∀ (q : Fin 215) (b : Bool),
    (machineFrom K).transition q b = KDense215.machine215.transition q b := by
  decide +kernel

theorem literal_parent : machineFrom K = KDense215.machine215 := by
  exact congrArg Machine.mk (funext fun q => funext fun b => parent_rows q b)

/-- The exact published K215 and exact CM215 alternative are equihalting. -/
theorem repo_blank_halts_iff :
    KDenseBridge.BlankHalts KDense215.machine215 ↔
      KDenseBridge.BlankHalts (machineFrom M) := by
  change CoreBlankHalts KDense215.machine215 ↔ CoreBlankHalts (machineFrom M)
  rw [← literal_parent]
  exact core_blank_halts_iff

/-- Instantiate P with ZFC refutability and h with the existing K215 endpoint.
This theorem is conditional on h; it does not silently reprove that endpoint. -/
theorem inherit_calibration (P : Prop)
    (h : KDenseBridge.BlankHalts KDense215.machine215 ↔ P) :
    KDenseBridge.BlankHalts (machineFrom M) ↔ P :=
  repo_blank_halts_iff.symm.trans h

#print axioms repo_blank_halts_iff
#print axioms inherit_calibration
end CM215
