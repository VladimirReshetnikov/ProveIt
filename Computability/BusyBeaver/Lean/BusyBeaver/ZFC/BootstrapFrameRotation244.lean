import BusyBeaver.ZFC.BootRotation244Chunk010
import BusyBeaver.ZFC.Rotation244Simulation
import BusyBeaver.ZFC.LogicalSeed246

/-!
Whole-tape identification of the rotation244 startup target with the calibrated
logical seed. This is a shape adapter for any configuration represented by
that target. The final theorem links it to the complete407931-step blank run
through the separately checked final bootstrap group.
The seed calibration is reused unchanged from LogicalSeed246. The target is
the complete finite zipper specified by the rotation244 delivery and the
bootstrap generator, including every spare block and the zero exterior.
Mira-Cult, Jeff Ketchersid, Andrew James Wade and the ProveIt reductions retain
the attribution of the imported source and machine proofs.
-/
namespace SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244

open FiniteZipper Permutation252Frame Rotation244Simulation

def spares : List Nat := List.replicate 167 1

theorem spares_nonempty : spares ≠ [] := by decide +kernel

theorem physical_seed :
    vregs LogicalSeed246.initial.registers = [0, 0, 0, 3, 0, 0, 3, 0, 0] := by
  decide +kernel

theorem seed_tail : LogicalTailZero LogicalSeed246.initial.registers := by
  intro i
  simpa only [LogicalSeed246.initial, Nat.add_comm] using LogicalSeed246.tail_zero i

/-- A complete literal target, not a finite-support-only tape observation. -/
def target : ZipConfig 244 :=
  { state := some ⟨87, by decide⟩, head := -5,
    left := true :: List.replicate 9 false,
    right := List.replicate 181 false ++ [true] ++
      registerBits ([0, 0, 0, 3, 0, 0, 3, 0, 0] ++ spares) ++
      List.replicate 0 false }

theorem target_zip :
    dispatchZip dispatchRotation244 (-5) 9 0 LogicalSeed246.initial 181 spares =
      target := by
  decide +kernel

/-- The theorem is independent of the eventual final checkpoint module. -/
theorem frame_of_target {binary : Config 244} (hz : ZipRep binary target) :
    DispatchFrame64 dispatchRotation244 binary LogicalSeed246.initial 181 spares := by
  refine ⟨by decide, seed_tail, 9, 0, ?_⟩
  have hh : binary.head = -5 := hz.2.1
  rw [hh, target_zip]
  exact hz

theorem frame_of_checkpoint {binary : Config 244} {checkpoint : ZipConfig 244}
    (reached : ZipRep binary checkpoint) (shape : checkpoint = target) :
    DispatchFrame64 dispatchRotation244 binary LogicalSeed246.initial 181 spares := by
  rw [shape] at reached
  exact frame_of_target reached

theorem target_checkpoint :
    BootRotation244Chunk010.checkpoint407931 = target := by
  decide +kernel

theorem bootstrap_frame :
    Rotation244Simulation.DispatchFrame64 dispatchRotation244
      (machineRotation244.run 407931) LogicalSeed246.initial 181 spares :=
  frame_of_checkpoint BootRotation244Chunk010.bootstrap407931 target_checkpoint

end SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244
