import BusyBeaver.ZFC.BootRotation240Chunk008

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation240 BootRotation240Chunk008

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.block406528
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.reached406528
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.block408576
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.reached408576
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.block409600
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.reached409600
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.block409664
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk008.reached409664

example : zipBlock fastMachine 12 BootRotation240Chunk007.checkpoint402432 = checkpoint406528 := block406528

example : ZipRep (machineRotation240.run 406528) checkpoint406528 := reached406528

example : zipBlock fastMachine 11 checkpoint406528 = checkpoint408576 := block408576

example : ZipRep (machineRotation240.run 408576) checkpoint408576 := reached408576

example : zipBlock fastMachine 10 checkpoint408576 = checkpoint409600 := block409600

example : ZipRep (machineRotation240.run 409600) checkpoint409600 := reached409600

example : zipBlock fastMachine 6 checkpoint409600 = checkpoint409664 := block409664

example : ZipRep (machineRotation240.run 409664) checkpoint409664 := reached409664

example : (machineRotation240.run 409664).state = checkpoint409664.state := reached409664.1

example : (machineRotation240.run 409664).head = checkpoint409664.head := reached409664.2.1

example (p : Int) : Tape.read (machineRotation240.run 409664).tape p = frameRead checkpoint409664 p := read_eq_frameRead reached409664 p
