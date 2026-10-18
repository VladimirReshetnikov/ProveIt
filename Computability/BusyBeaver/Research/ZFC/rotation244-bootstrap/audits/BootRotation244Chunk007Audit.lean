import BusyBeaver.ZFC.BootRotation244Chunk007

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation244 BootRotation244Chunk007

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk007.block361472
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk007.reached361472
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk007.block377856
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk007.reached377856
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk007.block394240
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk007.reached394240

example : zipBlock fastMachine 14 BootRotation244Chunk006.checkpoint345088 = checkpoint361472 := block361472

example : ZipRep (machineRotation244.run 361472) checkpoint361472 := reached361472

example : zipBlock fastMachine 14 checkpoint361472 = checkpoint377856 := block377856

example : ZipRep (machineRotation244.run 377856) checkpoint377856 := reached377856

example : zipBlock fastMachine 14 checkpoint377856 = checkpoint394240 := block394240

example : ZipRep (machineRotation244.run 394240) checkpoint394240 := reached394240

example : (machineRotation244.run 394240).state = checkpoint394240.state := reached394240.1

example : (machineRotation244.run 394240).head = checkpoint394240.head := reached394240.2.1

example (p : Int) : Tape.read (machineRotation244.run 394240).tape p = frameRead checkpoint394240 p := read_eq_frameRead reached394240 p
