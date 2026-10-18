import BusyBeaver.ZFC.BootRouting245Chunk005

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245Chunk005

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.block230400
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.reached230400
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.block246784
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.reached246784
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.block263168
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.reached263168
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.block279552
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk005.reached279552

example : zipBlock fastMachine 14 BootRouting245Chunk004.checkpoint214016 = checkpoint230400 := block230400

example : ZipRep (machineRouting245.run 230400) checkpoint230400 := reached230400

example : zipBlock fastMachine 14 checkpoint230400 = checkpoint246784 := block246784

example : ZipRep (machineRouting245.run 246784) checkpoint246784 := reached246784

example : zipBlock fastMachine 14 checkpoint246784 = checkpoint263168 := block263168

example : ZipRep (machineRouting245.run 263168) checkpoint263168 := reached263168

example : zipBlock fastMachine 14 checkpoint263168 = checkpoint279552 := block279552

example : ZipRep (machineRouting245.run 279552) checkpoint279552 := reached279552

example : (machineRouting245.run 279552).state = checkpoint279552.state := reached279552.1

example : (machineRouting245.run 279552).head = checkpoint279552.head := reached279552.2.1

example (p : Int) : Tape.read (machineRouting245.run 279552).tape p = frameRead checkpoint279552 p := read_eq_frameRead reached279552 p
