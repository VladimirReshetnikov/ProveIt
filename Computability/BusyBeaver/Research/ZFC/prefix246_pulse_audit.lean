import BusyBeaver.ZFC.Prefix246Pulse

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper ZipperRuns Prefix246Pulse

#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Pulse.pulse_zero_zero
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Pulse.pulse_zero_one
#print axioms SetTheory.BusyBeaver.ZFC.Prefix246Pulse.pulse_core

example (h : Int) (l r : List Bool) :
    zipRun machinePrefix246 (zAt (oldStatePrefix246 75) h l (false :: false :: r)) 3 =
      leftAt (oldStatePrefix246 131) h l (true :: true :: r) := pulse_zero_zero h l r

example (h : Int) (l r : List Bool) :
    zipRun machinePrefix246 (zAt (oldStatePrefix246 75) h l (false :: true :: r)) 3 =
      leftAt (oldStatePrefix246 112) h l (false :: true :: r) := pulse_zero_one h l r

example (c : Config 246) (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt (oldStatePrefix246 75) h l (false :: b :: r))) :
    ZipRep (machinePrefix246.runFrom c 3)
      (leftAt (oldStatePrefix246 (if b then 112 else 131)) h l ((!b) :: true :: r)) := by
  cases b <;> exact pulse_core _ h l r hc

example (c : Config 246) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt (oldStatePrefix246 75) h l (false :: false :: r))) (pos : Int) :
    Tape.read (machinePrefix246.runFrom c 3).tape pos =
      frameRead (leftAt (oldStatePrefix246 131) h l (true :: true :: r)) pos :=
  read_eq_frameRead (pulse_core false h l r hc) pos
