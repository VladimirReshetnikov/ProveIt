import BusyBeaver.ZFC.BootstrapFrameRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper Permutation252Frame Routing245Simulation BootstrapFrameRouting245

#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.spares_nonempty
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.physical_seed
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.seed_tail
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.target_zip
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.frame_of_target
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.frame_of_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.target_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrameRouting245.bootstrap_frame

example : spares ≠ [] := spares_nonempty
example : vregs LogicalSeed246.initial.registers = [0, 0, 0, 3, 0, 0, 3, 0, 0] :=
  physical_seed
example (i : Nat) : LogicalSeed246.initial.registers (9 + i) = 0 := seed_tail i
example : target =
    ({ state := some ⟨88, by decide⟩, head := -5,
       left := true :: List.replicate 9 false,
       right := List.replicate 181 false ++ [true] ++
         registerBits ([0, 0, 0, 3, 0, 0, 3, 0, 0] ++ List.replicate 167 1) } : ZipConfig 245) := rfl
example : dispatchZip dispatchRouting245 (-5) 9 0 LogicalSeed246.initial 181 spares =
    target := target_zip
example (binary : Config 245) (h : ZipRep binary target) :
    DispatchFrame64 dispatchRouting245 binary LogicalSeed246.initial 181 spares :=
  frame_of_target h
example (binary : Config 245) (checkpoint : ZipConfig 245)
    (h : ZipRep binary checkpoint) (hs : checkpoint = target) :
    DispatchFrame64 dispatchRouting245 binary LogicalSeed246.initial 181 spares :=
  frame_of_checkpoint h hs
example : BootRouting245Chunk009.checkpoint407915 = target := target_checkpoint
example : DispatchFrame64 dispatchRouting245 (machineRouting245.run 407915)
    LogicalSeed246.initial 181 spares := bootstrap_frame
