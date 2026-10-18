import BusyBeaver.ZFC.BootPrefix246Chunk004

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk004

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.block214016
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.reached214016
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.block230400
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.reached230400
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.block246784
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.reached246784
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.block263168
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk004.reached263168

example : zipBlock fastMachine 14 BootPrefix246Chunk003.checkpoint197632 = checkpoint214016 := block214016

example : ZipRep (machinePrefix246.run 214016) checkpoint214016 := reached214016

example : zipBlock fastMachine 14 checkpoint214016 = checkpoint230400 := block230400

example : ZipRep (machinePrefix246.run 230400) checkpoint230400 := reached230400

example : zipBlock fastMachine 14 checkpoint230400 = checkpoint246784 := block246784

example : ZipRep (machinePrefix246.run 246784) checkpoint246784 := reached246784

example : zipBlock fastMachine 14 checkpoint246784 = checkpoint263168 := block263168

example : ZipRep (machinePrefix246.run 263168) checkpoint263168 := reached263168

example : (machinePrefix246.run 263168).state = checkpoint263168.state := reached263168.1

example : (machinePrefix246.run 263168).head = checkpoint263168.head := reached263168.2.1

example (p : Int) : Tape.read (machinePrefix246.run 263168).tape p = frameRead checkpoint263168 p :=
  read_eq_frameRead reached263168 p
