import BusyBeaver.ZFC.BootPrefix246Chunk005

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk005

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.block279552
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.reached279552
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.block295936
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.reached295936
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.block312320
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.reached312320
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.block328704
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk005.reached328704

example : zipBlock fastMachine 14 BootPrefix246Chunk004.checkpoint263168 = checkpoint279552 := block279552

example : ZipRep (machinePrefix246.run 279552) checkpoint279552 := reached279552

example : zipBlock fastMachine 14 checkpoint279552 = checkpoint295936 := block295936

example : ZipRep (machinePrefix246.run 295936) checkpoint295936 := reached295936

example : zipBlock fastMachine 14 checkpoint295936 = checkpoint312320 := block312320

example : ZipRep (machinePrefix246.run 312320) checkpoint312320 := reached312320

example : zipBlock fastMachine 14 checkpoint312320 = checkpoint328704 := block328704

example : ZipRep (machinePrefix246.run 328704) checkpoint328704 := reached328704

example : (machinePrefix246.run 328704).state = checkpoint328704.state := reached328704.1

example : (machinePrefix246.run 328704).head = checkpoint328704.head := reached328704.2.1

example (p : Int) : Tape.read (machinePrefix246.run 328704).tape p = frameRead checkpoint328704 p :=
  read_eq_frameRead reached328704 p
