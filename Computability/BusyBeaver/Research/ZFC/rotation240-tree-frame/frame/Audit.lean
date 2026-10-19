import BusyBeaver.ZFC.BootstrapFrameRotation240

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper Permutation252Frame Rotation240Simulation BootstrapFrameRotation240

#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.spares_nonempty
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.physical_seed
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.seed_tail
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.target_zip
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.frame_of_target
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.frame_of_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.target_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRotation240.bootstrap_frame

example : spares ≠ [] := spares_nonempty
example : vregs LogicalSeed246.initial.registers = [0, 0, 0, 3, 0, 0, 3, 0, 0] :=
  physical_seed
example (i : Nat) : LogicalSeed246.initial.registers (9 + i) = 0 := seed_tail i
example : target =
    ({ state := some ⟨84, by decide⟩, head := -5,
       left := true :: List.replicate 9 false,
       right := List.replicate 181 false ++ [true] ++
         registerBits ([0, 0, 0, 3, 0, 0, 3, 0, 0] ++ List.replicate 167 1) ++
         List.replicate 0 false } : ZipConfig 240) := rfl
example : dispatchZip dispatchRotation240 (-5) 9 0 LogicalSeed246.initial 181 spares =
    target := target_zip
example (binary : Config 240) (h : ZipRep binary target) :
    DispatchFrame64 dispatchRotation240 binary LogicalSeed246.initial 181 spares :=
  frame_of_target h
example (binary : Config 240) (checkpoint : ZipConfig 240)
    (h : ZipRep binary checkpoint) (hs : checkpoint = target) :
    DispatchFrame64 dispatchRotation240 binary LogicalSeed246.initial 181 spares :=
  frame_of_checkpoint h hs
example : BootRotation240Chunk009.checkpoint409691 = target := target_checkpoint
example : DispatchFrame64 dispatchRotation240 (machineRotation240.run 409691)
    LogicalSeed246.initial 181 spares := bootstrap_frame
