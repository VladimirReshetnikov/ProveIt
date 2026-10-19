import BusyBeaver.ZFC.BootstrapFrameRotation244

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper Permutation252Frame Rotation244Simulation BootstrapFrameRotation244

#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.spares_nonempty
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.physical_seed
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.seed_tail
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.target_zip
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.frame_of_target
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.frame_of_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.target_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation244.bootstrap_frame

example : spares ≠ [] := spares_nonempty
example : vregs LogicalSeed246.initial.registers = [0, 0, 0, 3, 0, 0, 3, 0, 0] :=
  physical_seed
example (i : Nat) : LogicalSeed246.initial.registers (9 + i) = 0 := seed_tail i
example : target =
    ({ state := some ⟨87, by decide⟩, head := -5,
       left := true :: List.replicate 9 false,
       right := List.replicate 181 false ++ [true] ++
         registerBits ([0, 0, 0, 3, 0, 0, 3, 0, 0] ++ List.replicate 167 1) ++
         List.replicate 0 false } : ZipConfig 244) := rfl
example : dispatchZip dispatchRotation244 (-5) 9 0 LogicalSeed246.initial 181 spares =
    target := target_zip
example (binary : Config 244) (h : ZipRep binary target) :
    DispatchFrame64 dispatchRotation244 binary LogicalSeed246.initial 181 spares :=
  frame_of_target h
example (binary : Config 244) (checkpoint : ZipConfig 244)
    (h : ZipRep binary checkpoint) (hs : checkpoint = target) :
    DispatchFrame64 dispatchRotation244 binary LogicalSeed246.initial 181 spares :=
  frame_of_checkpoint h hs
example : BootRotation244Chunk010.checkpoint407931 = target := target_checkpoint
example : DispatchFrame64 dispatchRotation244 (machineRotation244.run 407931)
    LogicalSeed246.initial 181 spares := bootstrap_frame
