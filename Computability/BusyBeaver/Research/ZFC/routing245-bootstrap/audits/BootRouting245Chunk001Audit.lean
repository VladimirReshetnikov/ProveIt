import BusyBeaver.ZFC.BootRouting245Chunk001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245Chunk001

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk001.block17408
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk001.reached17408

example : zipBlock fastMachine 14 BootRouting245First.checkpoint1024 = checkpoint17408 := block17408

example : ZipRep (machineRouting245.run 17408) checkpoint17408 := reached17408

example : (machineRouting245.run 17408).state = checkpoint17408.state := reached17408.1

example : (machineRouting245.run 17408).head = checkpoint17408.head := reached17408.2.1

example (p : Int) : Tape.read (machineRouting245.run 17408).tape p = frameRead checkpoint17408 p := read_eq_frameRead reached17408 p
