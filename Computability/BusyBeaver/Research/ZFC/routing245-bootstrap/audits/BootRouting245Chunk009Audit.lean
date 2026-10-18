import BusyBeaver.ZFC.BootRouting245Chunk009

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245Chunk009

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.block407904
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.reached407904
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.block407912
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.reached407912
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.block407914
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.reached407914
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.block407915
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.reached407915
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.bootstrap407915
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.bootstrap_active_through

example : zipBlock fastMachine 5 BootRouting245Chunk008.checkpoint407872 = checkpoint407904 := block407904

example : ZipRep (machineRouting245.run 407904) checkpoint407904 := reached407904

example : zipBlock fastMachine 3 checkpoint407904 = checkpoint407912 := block407912

example : ZipRep (machineRouting245.run 407912) checkpoint407912 := reached407912

example : zipBlock fastMachine 1 checkpoint407912 = checkpoint407914 := block407914

example : ZipRep (machineRouting245.run 407914) checkpoint407914 := reached407914

example : zipBlock fastMachine 0 checkpoint407914 = checkpoint407915 := block407915

example : ZipRep (machineRouting245.run 407915) checkpoint407915 := reached407915

example : ZipRep (machineRouting245.run 407915) checkpoint407915 := bootstrap407915

example (t : Nat) (h : t ≤ 407915) : (machineRouting245.run t).state ≠ none := bootstrap_active_through t h

example : (machineRouting245.run 407915).state = checkpoint407915.state := reached407915.1

example : (machineRouting245.run 407915).head = checkpoint407915.head := reached407915.2.1

example (p : Int) : Tape.read (machineRouting245.run 407915).tape p = frameRead checkpoint407915 p := read_eq_frameRead reached407915 p
