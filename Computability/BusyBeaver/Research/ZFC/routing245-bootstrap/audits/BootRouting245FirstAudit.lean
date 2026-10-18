import BusyBeaver.ZFC.BootRouting245First

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245First

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245First.checkpoint0_rep
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245First.advance_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245First.block1024
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245First.first1024

example : ZipRep (initial 245) checkpoint0 := checkpoint0_rep

example (elapsed depth : Nat) {z z' : ZipConfig 245} (h : ZipRep (machineRouting245.run elapsed) z) (hc : zipBlock fastMachine depth z = z') : ZipRep (machineRouting245.run (elapsed + 2 ^ depth)) z' := advance_checkpoint elapsed depth h hc

example : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := block1024

example : ZipRep (machineRouting245.run 1024) checkpoint1024 := first1024

example : (machineRouting245.run 1024).state = checkpoint1024.state := first1024.1

example : (machineRouting245.run 1024).head = checkpoint1024.head := first1024.2.1

example (p : Int) : Tape.read (machineRouting245.run 1024).tape p = frameRead checkpoint1024 p := read_eq_frameRead first1024 p
