import BusyBeaver.ZFC.BootPrefix246Probe16384
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper FastTablePrefix246 BootPrefix246Probe16384

#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Probe16384.local16384
#print axioms SetTheory.BusyBeaver.ZFC.BootPrefix246Probe16384.transfer16384

example : zipBlock fastMachine 14 start = finish := local16384

example {c : Config 246} (h : ZipRep c start) :
    ZipRep (machinePrefix246.runFrom c 16384) finish := transfer16384 h

example {c : Config 246} (h : ZipRep c start) :
    (machinePrefix246.runFrom c 16384).state = finish.state := (transfer16384 h).1

example {c : Config 246} (h : ZipRep c start) (pos : Int) :
    Tape.read (machinePrefix246.runFrom c 16384).tape pos = frameRead finish pos :=
  read_eq_frameRead (transfer16384 h) pos
