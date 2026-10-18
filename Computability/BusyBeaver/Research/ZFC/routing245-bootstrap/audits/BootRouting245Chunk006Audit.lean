import BusyBeaver.ZFC.BootRouting245Chunk006

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245Chunk006

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.block295936
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.reached295936
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.block312320
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.reached312320
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.block328704
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.reached328704
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.block345088
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk006.reached345088

example : zipBlock fastMachine 14 BootRouting245Chunk005.checkpoint279552 = checkpoint295936 := block295936

example : ZipRep (machineRouting245.run 295936) checkpoint295936 := reached295936

example : zipBlock fastMachine 14 checkpoint295936 = checkpoint312320 := block312320

example : ZipRep (machineRouting245.run 312320) checkpoint312320 := reached312320

example : zipBlock fastMachine 14 checkpoint312320 = checkpoint328704 := block328704

example : ZipRep (machineRouting245.run 328704) checkpoint328704 := reached328704

example : zipBlock fastMachine 14 checkpoint328704 = checkpoint345088 := block345088

example : ZipRep (machineRouting245.run 345088) checkpoint345088 := reached345088

example : (machineRouting245.run 345088).state = checkpoint345088.state := reached345088.1

example : (machineRouting245.run 345088).head = checkpoint345088.head := reached345088.2.1

example (p : Int) : Tape.read (machineRouting245.run 345088).tape p = frameRead checkpoint345088 p := read_eq_frameRead reached345088 p
