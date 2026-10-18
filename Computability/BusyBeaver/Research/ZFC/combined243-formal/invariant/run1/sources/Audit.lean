import BusyBeaver.ZFC.Rotation244Invariant

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.Rotation244Invariant

#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Invariant.start_holds
#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Invariant.initial_holds
#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Invariant.step_holds
#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Invariant.runFrom_holds
#print axioms SetTheory.BusyBeaver.ZFC.Rotation244Invariant.run_holds

example (h : Int) (T : Tape) :
    Holds ⟨some (oldStateRotation244 95), h, T⟩ := start_holds h T

example : Holds (initial 244) := initial_holds

example (c : Config 244) (hc : Holds c) :
    Holds (machineRotation244.step c) := step_holds c hc

example (c : Config 244) (hc : Holds c) (t : Nat) :
    Holds (machineRotation244.runFrom c t) := runFrom_holds c hc t

example (t : Nat) : Holds (machineRotation244.run t) := run_holds t

example (c : Config 244) (hc : Holds c) (t : Nat)
    (hs : (machineRotation244.runFrom c t).state = some (oldStateRotation244 68)) :
    Tape.read (machineRotation244.runFrom c t).tape
      ((machineRotation244.runFrom c t).head - 1) = true :=
  (runFrom_holds c hc t).1 hs

example (c : Config 244) (hc : Holds c) (t : Nat)
    (hs : (machineRotation244.runFrom c t).state = some (oldStateRotation244 81))
    (hb : Tape.read (machineRotation244.runFrom c t).tape
      ((machineRotation244.runFrom c t).head - 1) = true) :
    Tape.read (machineRotation244.runFrom c t).tape
      ((machineRotation244.runFrom c t).head - 2) = true :=
  (runFrom_holds c hc t).2.1 hs hb

example (c : Config 244) (hc : Holds c) (t : Nat)
    (hs : (machineRotation244.runFrom c t).state = some (oldStateRotation244 167)) :
    Tape.read (machineRotation244.runFrom c t).tape
      ((machineRotation244.runFrom c t).head - 1) = true :=
  (runFrom_holds c hc t).2.2 hs
