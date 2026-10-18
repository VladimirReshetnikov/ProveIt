import BusyBeaver.ZFC.Rotation244Pulse

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open FiniteZipper ZipperRuns Rotation244Pulse

#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Pulse.pulse_zero_zero
#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Pulse.pulse_zero_one
#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Pulse.pulse_core

example (h : Int) (l r : List Bool) :
    zipRun machineRotation244 (zAt (oldStateRotation244 75) h l (false :: false :: r)) 3 =
      leftAt (oldStateRotation244 131) h l (true :: true :: r) := pulse_zero_zero h l r

example (h : Int) (l r : List Bool) :
    zipRun machineRotation244 (zAt (oldStateRotation244 75) h l (false :: true :: r)) 3 =
      leftAt (oldStateRotation244 112) h l (false :: true :: r) := pulse_zero_one h l r

example (c : Config 244) (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt (oldStateRotation244 75) h l (false :: b :: r))) :
    ZipRep (machineRotation244.runFrom c 3)
      (leftAt (oldStateRotation244 (if b then 112 else 131)) h l ((!b) :: true :: r)) := by
  cases b <;> exact pulse_core _ h l r hc

example (c : Config 244) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt (oldStateRotation244 75) h l (false :: false :: r))) (pos : Int) :
    Tape.read (machineRotation244.runFrom c 3).tape pos =
      frameRead (leftAt (oldStateRotation244 131) h l (true :: true :: r)) pos :=
  read_eq_frameRead (pulse_core false h l r hc) pos
