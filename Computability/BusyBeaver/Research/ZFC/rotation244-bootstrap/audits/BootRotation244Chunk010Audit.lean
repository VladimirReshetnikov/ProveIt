import BusyBeaver.ZFC.BootRotation244Chunk010

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation244 BootRotation244Chunk010

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk010.block407930
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk010.reached407930
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk010.block407931
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk010.reached407931
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk010.bootstrap407931
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk010.bootstrap_active_through

example : zipBlock fastMachine 1 BootRotation244Chunk009.checkpoint407928 = checkpoint407930 := block407930

example : ZipRep (machineRotation244.run 407930) checkpoint407930 := reached407930

example : zipBlock fastMachine 0 checkpoint407930 = checkpoint407931 := block407931

example : ZipRep (machineRotation244.run 407931) checkpoint407931 := reached407931

example : ZipRep (machineRotation244.run 407931) checkpoint407931 := bootstrap407931

example (t : Nat) (h : t ≤ 407931) : (machineRotation244.run t).state ≠ none := bootstrap_active_through t h

example : (machineRotation244.run 407931).state = checkpoint407931.state := reached407931.1

example : (machineRotation244.run 407931).head = checkpoint407931.head := reached407931.2.1

example (p : Int) : Tape.read (machineRotation244.run 407931).tape p = frameRead checkpoint407931 p := read_eq_frameRead reached407931 p
