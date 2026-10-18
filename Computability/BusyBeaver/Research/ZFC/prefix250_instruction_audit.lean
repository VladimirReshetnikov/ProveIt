import BusyBeaver.ZFC.InstructionPrefix250

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath Permutation252Frame SymbolicPrefix250 SitePrefix250
open InstructionPrefix250

#print axioms InstructionPrefix250.incRev_length
#print axioms InstructionPrefix250.incPath_length
#print axioms InstructionPrefix250.stripPath_length
#print axioms InstructionPrefix250.breakPath_length
#print axioms InstructionPrefix250.continuePath_length
#print axioms InstructionPrefix250.execute_frame
#print axioms InstructionPrefix250.halt_frame

example (P : List Bool) : (incRev P).length = P.length := incRev_length P

example (P : List Bool) : (incPath P).length = P.length := incPath_length P

example (b : Bool) (k : Nat) (P : List Bool) :
    (stripPath b k P).length ≤ P.length := stripPath_length b k P

example (k : Nat) (P : List Bool) :
    (breakPath k P).length ≤ P.length := breakPath_length k P

example (k : Nat) (P : List Bool) :
    (continuePath k P).length ≤ P.length := continuePath_length k P

example (Q : List Bool) (e : Edge) (R : Registers)
    (spares : List Nat) (n : Nat) (binary : Config 250) (next : Configuration)
    (hcheck : checkSite Q e = true) (htail : LogicalTailZero R)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary)
    (he : execute e Q R = some next) :
    ∃ k : Nat, 0 < k ∧ ∃ gap spares', spares' ≠ [] ∧
      DispatchFrame dispatch (machinePrefix250.runFrom binary k) next gap spares' :=
  execute_frame Q e R spares n binary next hcheck htail hspares hc he

example (Q : List Bool) (R : Registers) (spares : List Nat)
    (n : Nat) (binary : Config 250) (hcheck : checkSite Q .halt = true)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary) :
    ∃ k : Nat, 0 < k ∧ (machinePrefix250.runFrom binary k).state = none :=
  halt_frame Q R spares n binary hcheck hspares hc
