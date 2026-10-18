import BusyBeaver.ZFC.BootPrefix246Chunk002

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk002

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block82944
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached82944
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block99328
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached99328
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block115712
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached115712
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block132096
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached132096

example : zipBlock fastMachine 14 BootPrefix246Chunk001.checkpoint66560 = checkpoint82944 := block82944

example : ZipRep (machinePrefix246.run 82944) checkpoint82944 := reached82944

example : zipBlock fastMachine 14 checkpoint82944 = checkpoint99328 := block99328

example : ZipRep (machinePrefix246.run 99328) checkpoint99328 := reached99328

example : zipBlock fastMachine 14 checkpoint99328 = checkpoint115712 := block115712

example : ZipRep (machinePrefix246.run 115712) checkpoint115712 := reached115712

example : zipBlock fastMachine 14 checkpoint115712 = checkpoint132096 := block132096

example : ZipRep (machinePrefix246.run 132096) checkpoint132096 := reached132096

example : (machinePrefix246.run 132096).state = checkpoint132096.state := reached132096.1

example : (machinePrefix246.run 132096).head = checkpoint132096.head := reached132096.2.1

example (p : Int) : Tape.read (machinePrefix246.run 132096).tape p = frameRead checkpoint132096 p :=
  read_eq_frameRead reached132096 p
