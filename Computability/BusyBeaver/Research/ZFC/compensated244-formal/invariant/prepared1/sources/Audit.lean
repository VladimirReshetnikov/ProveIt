import BusyBeaver.ZFC.Routing245Invariant

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.Routing245Invariant

#print axioms start_holds
#print axioms initial_holds
#print axioms step_holds
#print axioms runFrom_holds
#print axioms run_holds

example (h : Int) (T : Tape) :
    Holds ⟨some (oldStateRouting245 95), h, T⟩ := start_holds h T

example : Holds (initial 245) := initial_holds

example (c : Config 245) (hc : Holds c) :
    Holds (machineRouting245.step c) := step_holds c hc

example (c : Config 245) (hc : Holds c) (t : Nat) :
    Holds (machineRouting245.runFrom c t) := runFrom_holds c hc t

example (t : Nat) : Holds (machineRouting245.run t) := run_holds t

example (c : Config 245) (hc : Holds c) (t : Nat)
    (hs : (machineRouting245.runFrom c t).state = some (oldStateRouting245 68)) :
    Tape.read (machineRouting245.runFrom c t).tape
      ((machineRouting245.runFrom c t).head - 1) = true :=
  (runFrom_holds c hc t).1 hs

example (c : Config 245) (hc : Holds c) (t : Nat)
    (hs : (machineRouting245.runFrom c t).state = some (oldStateRouting245 81))
    (hb : Tape.read (machineRouting245.runFrom c t).tape
      ((machineRouting245.runFrom c t).head - 1) = true) :
    Tape.read (machineRouting245.runFrom c t).tape
      ((machineRouting245.runFrom c t).head - 2) = true :=
  (runFrom_holds c hc t).2.1 hs hb

example (c : Config 245) (hc : Holds c) (t : Nat)
    (hs : (machineRouting245.runFrom c t).state = some (oldStateRouting245 167)) :
    Tape.read (machineRouting245.runFrom c t).tape
      ((machineRouting245.runFrom c t).head - 1) = true :=
  (runFrom_holds c hc t).2.2 hs
