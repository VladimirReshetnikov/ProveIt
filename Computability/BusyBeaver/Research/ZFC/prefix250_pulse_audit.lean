import BusyBeaver.ZFC.Prefix250Pulse

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open Prefix250Pulse FiniteZipper ZipperRuns

#print axioms pulseSafe_step
#print axioms pulseSafe_runFrom
#print axioms pulse_zero
#print axioms pulse_core
#print axioms blank_first_step
#print axioms safe_after_first
#print axioms recurrent_entry_reads_one
#print axioms initializer_only_at_zero

example (h : Int) (l r : List Bool) :
    zipRun machinePrefix250
      (zAt (oldStatePrefix250 75) h l (false :: false :: r)) 3 =
    leftAt (oldStatePrefix250 131) h l (true :: true :: r) :=
  pulse_zero_zero h l r

example (h : Int) (l r : List Bool) :
    zipRun machinePrefix250
      (zAt (oldStatePrefix250 75) h l (false :: true :: r)) 3 =
    leftAt (oldStatePrefix250 112) h l (false :: true :: r) :=
  pulse_zero_one h l r

example {c : Config 250} (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt (oldStatePrefix250 75) h l (false :: b :: r))) :
    ZipRep (machinePrefix250.runFrom c 3)
      (leftAt (if b then oldStatePrefix250 112 else oldStatePrefix250 131)
        h l ((!b) :: true :: r)) := pulse_core b h l r hc

example (t : Nat)
    (hs : (machinePrefix250.run (t + 1)).state = some (oldStatePrefix250 97)) :
    Tape.read (machinePrefix250.run (t + 1)).tape
      (machinePrefix250.run (t + 1)).head = true := recurrent_entry_reads_one t hs

example (t : Nat)
    (hs : (machinePrefix250.run t).state = some (oldStatePrefix250 97))
    (hb : Tape.read (machinePrefix250.run t).tape
      (machinePrefix250.run t).head = false) : t = 0 := initializer_only_at_zero t hs hb
