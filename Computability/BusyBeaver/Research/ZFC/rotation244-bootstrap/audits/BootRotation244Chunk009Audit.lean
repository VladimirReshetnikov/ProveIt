import BusyBeaver.ZFC.BootRotation244Chunk009

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTableRotation244 BootRotation244Chunk009

#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.block407872
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.reached407872
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.block407904
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.reached407904
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.block407920
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.reached407920
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.block407928
#print axioms SetTheory.BusyBeaver.ZFC.BootRotation244Chunk009.reached407928

example : zipBlock fastMachine 6 BootRotation244Chunk008.checkpoint407808 = checkpoint407872 := block407872

example : ZipRep (machineRotation244.run 407872) checkpoint407872 := reached407872

example : zipBlock fastMachine 5 checkpoint407872 = checkpoint407904 := block407904

example : ZipRep (machineRotation244.run 407904) checkpoint407904 := reached407904

example : zipBlock fastMachine 4 checkpoint407904 = checkpoint407920 := block407920

example : ZipRep (machineRotation244.run 407920) checkpoint407920 := reached407920

example : zipBlock fastMachine 3 checkpoint407920 = checkpoint407928 := block407928

example : ZipRep (machineRotation244.run 407928) checkpoint407928 := reached407928

example : (machineRotation244.run 407928).state = checkpoint407928.state := reached407928.1

example : (machineRotation244.run 407928).head = checkpoint407928.head := reached407928.2.1

example (p : Int) : Tape.read (machineRotation244.run 407928).tape p = frameRead checkpoint407928 p := read_eq_frameRead reached407928 p
