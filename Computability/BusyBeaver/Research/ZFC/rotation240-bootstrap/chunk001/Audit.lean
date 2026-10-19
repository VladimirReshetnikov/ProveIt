import BusyBeaver.ZFC.BootRotation240Chunk001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation240 BootRotation240Chunk001

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk001.block17408
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation240Chunk001.reached17408

example : zipBlock fastMachine 14 BootRotation240First.checkpoint1024 = checkpoint17408 := block17408

example : ZipRep (machineRotation240.run 17408) checkpoint17408 := reached17408

example : (machineRotation240.run 17408).state = checkpoint17408.state := reached17408.1

example : (machineRotation240.run 17408).head = checkpoint17408.head := reached17408.2.1

example (p : Int) : Tape.read (machineRotation240.run 17408).tape p = frameRead checkpoint17408 p := read_eq_frameRead reached17408 p
