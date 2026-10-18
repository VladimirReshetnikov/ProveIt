import BusyBeaver.ZFC.BootRouting245Chunk008

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245Chunk008

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.block406528
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.reached406528
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.block407552
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.reached407552
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.block407808
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.reached407808
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.block407872
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk008.reached407872

example : zipBlock fastMachine 12 BootRouting245Chunk007.checkpoint402432 = checkpoint406528 := block406528

example : ZipRep (machineRouting245.run 406528) checkpoint406528 := reached406528

example : zipBlock fastMachine 10 checkpoint406528 = checkpoint407552 := block407552

example : ZipRep (machineRouting245.run 407552) checkpoint407552 := reached407552

example : zipBlock fastMachine 8 checkpoint407552 = checkpoint407808 := block407808

example : ZipRep (machineRouting245.run 407808) checkpoint407808 := reached407808

example : zipBlock fastMachine 6 checkpoint407808 = checkpoint407872 := block407872

example : ZipRep (machineRouting245.run 407872) checkpoint407872 := reached407872

example : (machineRouting245.run 407872).state = checkpoint407872.state := reached407872.1

example : (machineRouting245.run 407872).head = checkpoint407872.head := reached407872.2.1

example (p : Int) : Tape.read (machineRouting245.run 407872).tape p = frameRead checkpoint407872 p := read_eq_frameRead reached407872 p
