import BusyBeaver.ZFC.BootPrefix246Chunk003

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk003

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.block148480
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.reached148480
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.block164864
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.reached164864
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.block181248
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.reached181248
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.block197632
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk003.reached197632

example : zipBlock fastMachine 14 BootPrefix246Chunk002.checkpoint132096 = checkpoint148480 := block148480

example : ZipRep (machinePrefix246.run 148480) checkpoint148480 := reached148480

example : zipBlock fastMachine 14 checkpoint148480 = checkpoint164864 := block164864

example : ZipRep (machinePrefix246.run 164864) checkpoint164864 := reached164864

example : zipBlock fastMachine 14 checkpoint164864 = checkpoint181248 := block181248

example : ZipRep (machinePrefix246.run 181248) checkpoint181248 := reached181248

example : zipBlock fastMachine 14 checkpoint181248 = checkpoint197632 := block197632

example : ZipRep (machinePrefix246.run 197632) checkpoint197632 := reached197632

example : (machinePrefix246.run 197632).state = checkpoint197632.state := reached197632.1

example : (machinePrefix246.run 197632).head = checkpoint197632.head := reached197632.2.1

example (p : Int) : Tape.read (machinePrefix246.run 197632).tape p = frameRead checkpoint197632 p :=
  read_eq_frameRead reached197632 p
