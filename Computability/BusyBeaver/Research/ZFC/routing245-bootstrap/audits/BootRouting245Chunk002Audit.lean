import BusyBeaver.ZFC.BootRouting245Chunk002

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRouting245 BootRouting245Chunk002

#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.block33792
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.reached33792
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.block50176
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.reached50176
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.block66560
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.reached66560
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.block82944
#print axioms SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002.reached82944

example : zipBlock fastMachine 14 BootRouting245Chunk001.checkpoint17408 = checkpoint33792 := block33792

example : ZipRep (machineRouting245.run 33792) checkpoint33792 := reached33792

example : zipBlock fastMachine 14 checkpoint33792 = checkpoint50176 := block50176

example : ZipRep (machineRouting245.run 50176) checkpoint50176 := reached50176

example : zipBlock fastMachine 14 checkpoint50176 = checkpoint66560 := block66560

example : ZipRep (machineRouting245.run 66560) checkpoint66560 := reached66560

example : zipBlock fastMachine 14 checkpoint66560 = checkpoint82944 := block82944

example : ZipRep (machineRouting245.run 82944) checkpoint82944 := reached82944

example : (machineRouting245.run 82944).state = checkpoint82944.state := reached82944.1

example : (machineRouting245.run 82944).head = checkpoint82944.head := reached82944.2.1

example (p : Int) : Tape.read (machineRouting245.run 82944).tape p = frameRead checkpoint82944 p := read_eq_frameRead reached82944 p
