import BusyBeaver.ZFC.Rotation240Pulse

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper ZipperRuns Rotation240Pulse

#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Pulse.pulse_zero_zero
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Pulse.pulse_zero_one
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Pulse.pulse_core

example (h : Int) (l r : List Bool) :
    zipRun machineRotation240 (zAt (oldStateRotation240 75) h l (false :: false :: r)) 3 =
      leftAt (oldStateRotation240 131) h l (true :: true :: r) := pulse_zero_zero h l r

example (h : Int) (l r : List Bool) :
    zipRun machineRotation240 (zAt (oldStateRotation240 75) h l (false :: true :: r)) 3 =
      leftAt (oldStateRotation240 112) h l (false :: true :: r) := pulse_zero_one h l r

example (c : Config 240) (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt (oldStateRotation240 75) h l (false :: b :: r))) :
    ZipRep (machineRotation240.runFrom c 3)
      (leftAt (oldStateRotation240 (if b then 112 else 131)) h l ((!b) :: true :: r)) := by
  cases b <;> exact pulse_core _ h l r hc

example (c : Config 240) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt (oldStateRotation240 75) h l (false :: false :: r))) (pos : Int) :
    Tape.read (machineRotation240.runFrom c 3).tape pos =
      frameRead (leftAt (oldStateRotation240 131) h l (true :: true :: r)) pos :=
  read_eq_frameRead (pulse_core false h l r hc) pos
