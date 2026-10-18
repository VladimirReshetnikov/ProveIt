import BusyBeaver.ZFC.BootstrapFrame246

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper Permutation252Frame BootstrapFrame246

#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrame246.spares_nonempty
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrame246.physical_seed
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrame246.seed_tail
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrame246.target_zip
#print axioms SetTheory.BusyBeaver.ZFC.BootstrapFrame246.bootstrap_frame

example : spares ≠ [] := spares_nonempty
example : vregs LogicalSeed246.initial.registers = [0, 0, 0, 3, 0, 0, 3, 0, 0] := physical_seed
example (i : Nat) : LogicalSeed246.initial.registers (9 + i) = 0 := seed_tail i
example : dispatchZip dispatchPrefix246 (-5) 10 0 LogicalSeed246.initial 181 spares =
    BootPrefix246Probe16384.finish := target_zip
example : DispatchFrame dispatchPrefix246 (machinePrefix246.run 410735)
    LogicalSeed246.initial 181 spares := bootstrap_frame
