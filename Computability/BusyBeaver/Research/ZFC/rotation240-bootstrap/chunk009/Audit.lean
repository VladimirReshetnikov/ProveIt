import BusyBeaver.ZFC.BootRotation240Chunk009

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation240 BootRotation240Chunk009

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409680
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409680
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409688
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409688
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409690
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409690
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409691
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409691
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.bootstrap409691
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.bootstrap_active_through

example : zipBlock fastMachine 4 BootRotation240Chunk008.checkpoint409664 = checkpoint409680 := block409680

example : ZipRep (machineRotation240.run 409680) checkpoint409680 := reached409680

example : zipBlock fastMachine 3 checkpoint409680 = checkpoint409688 := block409688

example : ZipRep (machineRotation240.run 409688) checkpoint409688 := reached409688

example : zipBlock fastMachine 1 checkpoint409688 = checkpoint409690 := block409690

example : ZipRep (machineRotation240.run 409690) checkpoint409690 := reached409690

example : zipBlock fastMachine 0 checkpoint409690 = checkpoint409691 := block409691

example : ZipRep (machineRotation240.run 409691) checkpoint409691 := reached409691

example : ZipRep (machineRotation240.run 409691) checkpoint409691 := bootstrap409691

example (t : Nat) (h : t ≤ 409691) : (machineRotation240.run t).state ≠ none := bootstrap_active_through t h

example : (machineRotation240.run 409691).state = checkpoint409691.state := reached409691.1

example : (machineRotation240.run 409691).head = checkpoint409691.head := reached409691.2.1

example (p : Int) : Tape.read (machineRotation240.run 409691).tape p = frameRead checkpoint409691 p := read_eq_frameRead reached409691 p
