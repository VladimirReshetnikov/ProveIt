import BusyBeaver.ZFC.BootRotation240Chunk003

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation240 BootRotation240Chunk003

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.block99328
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.reached99328
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.block115712
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.reached115712
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.block132096
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.reached132096
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.block148480
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk003.reached148480

example : zipBlock fastMachine 14 BootRotation240Chunk002.checkpoint82944 = checkpoint99328 := block99328

example : ZipRep (machineRotation240.run 99328) checkpoint99328 := reached99328

example : zipBlock fastMachine 14 checkpoint99328 = checkpoint115712 := block115712

example : ZipRep (machineRotation240.run 115712) checkpoint115712 := reached115712

example : zipBlock fastMachine 14 checkpoint115712 = checkpoint132096 := block132096

example : ZipRep (machineRotation240.run 132096) checkpoint132096 := reached132096

example : zipBlock fastMachine 14 checkpoint132096 = checkpoint148480 := block148480

example : ZipRep (machineRotation240.run 148480) checkpoint148480 := reached148480

example : (machineRotation240.run 148480).state = checkpoint148480.state := reached148480.1

example : (machineRotation240.run 148480).head = checkpoint148480.head := reached148480.2.1

example (p : Int) : Tape.read (machineRotation240.run 148480).tape p = frameRead checkpoint148480 p := read_eq_frameRead reached148480 p
