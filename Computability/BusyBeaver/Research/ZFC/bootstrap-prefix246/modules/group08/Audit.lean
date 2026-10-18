import BusyBeaver.ZFC.BootPrefix246Chunk008

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Chunk008

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.block394350
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.reached394350
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.block394351
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.reached394351
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.bootstrap410735
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.bootstrap_state
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.bootstrap_head
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.bootstrap_tape
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.bootstrap_active_through

example : zipBlock fastMachine 1 BootPrefix246Chunk007.checkpoint394348 = checkpoint394350 := block394350

example : ZipRep (machinePrefix246.run 394350) checkpoint394350 := reached394350

example : zipBlock fastMachine 0 checkpoint394350 = checkpoint394351 := block394351

example : ZipRep (machinePrefix246.run 394351) checkpoint394351 := reached394351

example : ZipRep (machinePrefix246.run 410735) BootPrefix246Probe16384.finish := bootstrap410735

example : (machinePrefix246.run 410735).state = some ⟨88, by decide⟩ := bootstrap_state

example : (machinePrefix246.run 410735).head = -5 := bootstrap_head

example (p : Int) : Tape.read (machinePrefix246.run 410735).tape p = frameRead BootPrefix246Probe16384.finish p := bootstrap_tape p

example (t : Nat) (h : t ≤ 410735) : (machinePrefix246.run t).state ≠ none := bootstrap_active_through t h
