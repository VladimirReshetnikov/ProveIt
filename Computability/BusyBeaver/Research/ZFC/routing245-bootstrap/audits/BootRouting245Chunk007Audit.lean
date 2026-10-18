import BusyBeaver.ZFC.BootRouting245Chunk007

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245Chunk007

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.block361472
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.reached361472
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.block377856
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.reached377856
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.block394240
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.reached394240
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.block402432
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk007.reached402432

example : zipBlock fastMachine 14 BootRouting245Chunk006.checkpoint345088 = checkpoint361472 := block361472

example : ZipRep (machineRouting245.run 361472) checkpoint361472 := reached361472

example : zipBlock fastMachine 14 checkpoint361472 = checkpoint377856 := block377856

example : ZipRep (machineRouting245.run 377856) checkpoint377856 := reached377856

example : zipBlock fastMachine 14 checkpoint377856 = checkpoint394240 := block394240

example : ZipRep (machineRouting245.run 394240) checkpoint394240 := reached394240

example : zipBlock fastMachine 13 checkpoint394240 = checkpoint402432 := block402432

example : ZipRep (machineRouting245.run 402432) checkpoint402432 := reached402432

example : (machineRouting245.run 402432).state = checkpoint402432.state := reached402432.1

example : (machineRouting245.run 402432).head = checkpoint402432.head := reached402432.2.1

example (p : Int) : Tape.read (machineRouting245.run 402432).tape p = frameRead checkpoint402432 p := read_eq_frameRead reached402432 p
