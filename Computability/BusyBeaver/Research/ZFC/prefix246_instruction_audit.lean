import BusyBeaver.ZFC.InstructionPrefix246

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath Permutation252Frame SymbolicPrefix246 SitePrefix246
open InstructionPrefix246

#print axioms InstructionPrefix246.incRev_length
#print axioms InstructionPrefix246.incPath_length
#print axioms InstructionPrefix246.stripPath_length
#print axioms InstructionPrefix246.breakPath_length
#print axioms InstructionPrefix246.continuePath_length
#print axioms InstructionPrefix246.execute_frame
#print axioms InstructionPrefix246.halt_frame

example (P : List Bool) : (incRev P).length = P.length := incRev_length P

example (P : List Bool) : (incPath P).length = P.length := incPath_length P

example (b : Bool) (k : Nat) (P : List Bool) :
    (stripPath b k P).length ≤ P.length := stripPath_length b k P

example (k : Nat) (P : List Bool) :
    (breakPath k P).length ≤ P.length := breakPath_length k P

example (k : Nat) (P : List Bool) :
    (continuePath k P).length ≤ P.length := continuePath_length k P

example (Q : List Bool) (e : Edge) (R : Registers)
    (spares : List Nat) (n : Nat) (binary : Config 246) (next : Configuration)
    (hcheck : checkSite Q e = true) (htail : LogicalTailZero R)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary)
    (he : execute e Q R = some next) :
    ∃ k : Nat, 0 < k ∧ ∃ gap spares', spares' ≠ [] ∧
      DispatchFrame dispatch (machinePrefix246.runFrom binary k) next gap spares' :=
  execute_frame Q e R spares n binary next hcheck htail hspares hc he

example (Q : List Bool) (R : Registers) (spares : List Nat)
    (n : Nat) (binary : Config 246) (hcheck : checkSite Q .halt = true)
    (hspares : spares ≠ [])
    (hc : Represents n (vregs R ++ spares) (start Q) binary) :
    ∃ k : Nat, 0 < k ∧ (machinePrefix246.runFrom binary k).state = none :=
  halt_frame Q R spares n binary hcheck hspares hc
