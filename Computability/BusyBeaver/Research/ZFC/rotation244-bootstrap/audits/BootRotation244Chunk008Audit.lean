import BusyBeaver.ZFC.BootRotation244Chunk008

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation244 BootRotation244Chunk008

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.block402432
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.reached402432
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.block406528
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.reached406528
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.block407552
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.reached407552
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.block407808
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk008.reached407808

example : zipBlock fastMachine 13 BootRotation244Chunk007.checkpoint394240 = checkpoint402432 := block402432

example : ZipRep (machineRotation244.run 402432) checkpoint402432 := reached402432

example : zipBlock fastMachine 12 checkpoint402432 = checkpoint406528 := block406528

example : ZipRep (machineRotation244.run 406528) checkpoint406528 := reached406528

example : zipBlock fastMachine 10 checkpoint406528 = checkpoint407552 := block407552

example : ZipRep (machineRotation244.run 407552) checkpoint407552 := reached407552

example : zipBlock fastMachine 8 checkpoint407552 = checkpoint407808 := block407808

example : ZipRep (machineRotation244.run 407808) checkpoint407808 := reached407808

example : (machineRotation244.run 407808).state = checkpoint407808.state := reached407808.1

example : (machineRotation244.run 407808).head = checkpoint407808.head := reached407808.2.1

example (p : Int) : Tape.read (machineRotation244.run 407808).tape p = frameRead checkpoint407808 p := read_eq_frameRead reached407808 p
