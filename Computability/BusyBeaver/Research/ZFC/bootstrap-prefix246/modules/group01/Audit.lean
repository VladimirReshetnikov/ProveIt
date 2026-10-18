import BusyBeaver.ZFC.BootPrefix246Chunk001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk001

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.block17408
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.reached17408
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.block33792
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.reached33792
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.block50176
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.reached50176
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.block66560
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001.reached66560

example : zipBlock fastMachine 14 BootPrefix246First.checkpoint1024 = checkpoint17408 := block17408

example : ZipRep (machinePrefix246.run 17408) checkpoint17408 := reached17408

example : zipBlock fastMachine 14 checkpoint17408 = checkpoint33792 := block33792

example : ZipRep (machinePrefix246.run 33792) checkpoint33792 := reached33792

example : zipBlock fastMachine 14 checkpoint33792 = checkpoint50176 := block50176

example : ZipRep (machinePrefix246.run 50176) checkpoint50176 := reached50176

example : zipBlock fastMachine 14 checkpoint50176 = checkpoint66560 := block66560

example : ZipRep (machinePrefix246.run 66560) checkpoint66560 := reached66560

example : (machinePrefix246.run 66560).state = checkpoint66560.state := reached66560.1

example : (machinePrefix246.run 66560).head = checkpoint66560.head := reached66560.2.1

example (p : Int) : Tape.read (machinePrefix246.run 66560).tape p = frameRead checkpoint66560 p :=
  read_eq_frameRead reached66560 p
