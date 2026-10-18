import BusyBeaver.ZFC.BootPrefix246First

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246First

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246First.checkpoint0_rep
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246First.advance_checkpoint
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246First.first_block
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246First.first1024
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246First.first1024_state
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246First.first1024_head
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246First.first1024_tape

example : ZipRep (initial 246) checkpoint0 := checkpoint0_rep

example (elapsed depth : Nat) {z z' : ZipConfig 246}
    (h : ZipRep (machinePrefix246.run elapsed) z)
    (hc : zipBlock fastMachine depth z = z') :
    ZipRep (machinePrefix246.run (elapsed + 2 ^ depth)) z' := advance_checkpoint elapsed depth h hc

example : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := first_block

example : ZipRep (machinePrefix246.run 1024) checkpoint1024 := first1024

example : (machinePrefix246.run 1024).state = some ⟨88, by decide⟩ := first1024_state

example : (machinePrefix246.run 1024).head = -2 := first1024_head

example (p : Int) : Tape.read (machinePrefix246.run 1024).tape p = frameRead checkpoint1024 p :=
  first1024_tape p

example (i : Nat) : Tape.read (machinePrefix246.run 1024).tape
    (checkpoint1024.head - ((i + 1 : Nat) : Int)) = checkpoint1024.left.getD i false :=
  first1024.2.2.1 i

example (i : Nat) : Tape.read (machinePrefix246.run 1024).tape
    (checkpoint1024.head + (i : Int)) = checkpoint1024.right.getD i false :=
  first1024.2.2.2 i
