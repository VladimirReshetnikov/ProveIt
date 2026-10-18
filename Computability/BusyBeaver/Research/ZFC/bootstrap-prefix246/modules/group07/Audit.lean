import BusyBeaver.ZFC.BootPrefix246Chunk007

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk007

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.block394304
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.reached394304
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.block394336
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.reached394336
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.block394344
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.reached394344
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.block394348
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk007.reached394348

example : zipBlock fastMachine 6 BootPrefix246Chunk006.checkpoint394240 = checkpoint394304 := block394304

example : ZipRep (machinePrefix246.run 394304) checkpoint394304 := reached394304

example : zipBlock fastMachine 5 checkpoint394304 = checkpoint394336 := block394336

example : ZipRep (machinePrefix246.run 394336) checkpoint394336 := reached394336

example : zipBlock fastMachine 3 checkpoint394336 = checkpoint394344 := block394344

example : ZipRep (machinePrefix246.run 394344) checkpoint394344 := reached394344

example : zipBlock fastMachine 2 checkpoint394344 = checkpoint394348 := block394348

example : ZipRep (machinePrefix246.run 394348) checkpoint394348 := reached394348

example : (machinePrefix246.run 394348).state = checkpoint394348.state := reached394348.1

example : (machinePrefix246.run 394348).head = checkpoint394348.head := reached394348.2.1

example (p : Int) : Tape.read (machinePrefix246.run 394348).tape p = frameRead checkpoint394348 p :=
  read_eq_frameRead reached394348 p
