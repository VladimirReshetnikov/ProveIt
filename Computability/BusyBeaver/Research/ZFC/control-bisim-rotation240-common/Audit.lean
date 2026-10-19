import BusyBeaver.ZFC.ControlBisimRotation240Common

open SetTheory.BusyBeaver.ZFC
open ArithmeticControlBisim ControlBisimRotation240 ControlBisimRotation240Split

#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split.checkFrom_join
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split.chunk_join

example (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound i m n : Nat)
    (hl : checkFrom rowsA rowsB cert fuel bound i m = true)
    (hr : checkFrom rowsA rowsB cert fuel bound (i + m) n = true) :
    checkFrom rowsA rowsB cert fuel bound i (m + n) = true :=
  checkFrom_join rowsA rowsB cert fuel bound m i n hl hr

example (i m n : Nat) (hl : chunk i m = true) (hr : chunk (i + m) n = true) :
    chunk i (m + n) = true := chunk_join i m n hl hr
