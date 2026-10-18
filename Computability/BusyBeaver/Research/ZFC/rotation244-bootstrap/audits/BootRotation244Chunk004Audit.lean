import BusyBeaver.ZFC.BootRotation244Chunk004

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation244 BootRotation244Chunk004

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.block164864
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.reached164864
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.block181248
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.reached181248
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.block197632
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.reached197632
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.block214016
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk004.reached214016

example : zipBlock fastMachine 14 BootRotation244Chunk003.checkpoint148480 = checkpoint164864 := block164864

example : ZipRep (machineRotation244.run 164864) checkpoint164864 := reached164864

example : zipBlock fastMachine 14 checkpoint164864 = checkpoint181248 := block181248

example : ZipRep (machineRotation244.run 181248) checkpoint181248 := reached181248

example : zipBlock fastMachine 14 checkpoint181248 = checkpoint197632 := block197632

example : ZipRep (machineRotation244.run 197632) checkpoint197632 := reached197632

example : zipBlock fastMachine 14 checkpoint197632 = checkpoint214016 := block214016

example : ZipRep (machineRotation244.run 214016) checkpoint214016 := reached214016

example : (machineRotation244.run 214016).state = checkpoint214016.state := reached214016.1

example : (machineRotation244.run 214016).head = checkpoint214016.head := reached214016.2.1

example (p : Int) : Tape.read (machineRotation244.run 214016).tape p = frameRead checkpoint214016 p := read_eq_frameRead reached214016 p
