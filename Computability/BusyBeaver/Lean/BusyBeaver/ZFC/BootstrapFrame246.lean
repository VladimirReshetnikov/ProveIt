import BusyBeaver.ZFC.BootPrefix246Chunk008
import BusyBeaver.ZFC.Permutation252Frame
import BusyBeaver.ZFC.LogicalSeed246

/-!
Identify the exact contextual-fold246 blank startup with its logical seed.
The complete tape is retained, including all 167 value-one spare blocks.
The independent logical seed calibration is imported but the runtime and
all-sites composition are separate obligations. The reported finite shape
comes from source63; all equalities below are checked by Lean's kernel.
-/
namespace SetTheory.BusyBeaver.ZFC.BootstrapFrame246

open FiniteZipper Permutation252Frame

def spares : List Nat := List.replicate 167 1

theorem spares_nonempty : spares ≠ [] := by decide +kernel

theorem physical_seed :
    vregs LogicalSeed246.initial.registers = [0, 0, 0, 3, 0, 0, 3, 0, 0] := by
  decide +kernel

theorem seed_tail : LogicalTailZero LogicalSeed246.initial.registers := by
  intro i
  simpa only [LogicalSeed246.initial, Nat.add_comm] using LogicalSeed246.tail_zero i

/-- The finite zipper equality also fixes the omitted exterior to zero. -/
theorem target_zip :
    dispatchZip dispatchPrefix246 (-5) 10 0 LogicalSeed246.initial 181 spares =
      BootPrefix246Probe16384.finish := by
  decide +kernel

/-- The exact blank run reaches the whole dispatch frame of the calibrated seed. -/
theorem bootstrap_frame :
    DispatchFrame dispatchPrefix246 (machinePrefix246.run 410735)
      LogicalSeed246.initial 181 spares := by
  refine ⟨by decide, seed_tail, 10, 0, ?_⟩
  rw [BootPrefix246Chunk008.bootstrap_head, target_zip]
  exact BootPrefix246Chunk008.bootstrap410735

end SetTheory.BusyBeaver.ZFC.BootstrapFrame246
