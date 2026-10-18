import BusyBeaver.ZFC.BootPrefix246Chunk006

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk006

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.block345088
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.reached345088
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.block361472
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.reached361472
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.block377856
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.reached377856
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.block394240
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk006.reached394240

example : zipBlock fastMachine 14 BootPrefix246Chunk005.checkpoint328704 = checkpoint345088 := block345088

example : ZipRep (machinePrefix246.run 345088) checkpoint345088 := reached345088

example : zipBlock fastMachine 14 checkpoint345088 = checkpoint361472 := block361472

example : ZipRep (machinePrefix246.run 361472) checkpoint361472 := reached361472

example : zipBlock fastMachine 14 checkpoint361472 = checkpoint377856 := block377856

example : ZipRep (machinePrefix246.run 377856) checkpoint377856 := reached377856

example : zipBlock fastMachine 14 checkpoint377856 = checkpoint394240 := block394240

example : ZipRep (machinePrefix246.run 394240) checkpoint394240 := reached394240

example : (machinePrefix246.run 394240).state = checkpoint394240.state := reached394240.1

example : (machinePrefix246.run 394240).head = checkpoint394240.head := reached394240.2.1

example (p : Int) : Tape.read (machinePrefix246.run 394240).tape p = frameRead checkpoint394240 p :=
  read_eq_frameRead reached394240 p
