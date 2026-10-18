import BusyBeaver.ZFC.InstructionRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open Routing245Simulation
open RegisterPath Permutation252Frame SymbolicRouting245 SiteRouting245
open InstructionRouting245

#print axioms InstructionRouting245.incRev_length
#print axioms InstructionRouting245.incPath_length
#print axioms InstructionRouting245.stripPath_length
#print axioms InstructionRouting245.breakPath_length
#print axioms InstructionRouting245.continuePath_length
#print axioms InstructionRouting245.execute_frame
#print axioms InstructionRouting245.halt_frame

example (P : List Bool) : (incRev P).length = P.length := incRev_length P

example (P : List Bool) : (incPath P).length = P.length := incPath_length P

example (b : Bool) (k : Nat) (P : List Bool) :
    (stripPath b k P).length ≤ P.length := stripPath_length b k P

example (k : Nat) (P : List Bool) :
    (breakPath k P).length ≤ P.length := breakPath_length k P

example (k : Nat) (P : List Bool) :
    (continuePath k P).length ≤ P.length := continuePath_length k P

example (Q : List Bool) (e : Edge) (R : Registers)
    (spares : List Nat) (n : Nat) (binary : Config 245) (next : Configuration)
    (hcheck : checkSite Q e = true) (htail : LogicalTailZero R)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary)
    (he : execute e Q R = some next) :
    ∃ k : Nat, 0 < k ∧ ∃ gap spares', spares' ≠ [] ∧
      DispatchFrame64 dispatch (machineRouting245.runFrom binary k) next gap spares' :=
  execute_frame Q e R spares n binary next hcheck htail hspares hc he

example (Q : List Bool) (R : Registers) (spares : List Nat)
    (n : Nat) (binary : Config 245) (hcheck : checkSite Q .halt = true)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary) :
    ∃ k : Nat, 0 < k ∧ (machineRouting245.runFrom binary k).state = none :=
  halt_frame Q R spares n binary hcheck hspares hc
